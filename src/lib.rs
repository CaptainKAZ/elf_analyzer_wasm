// src/lib.rs
use wasm_bindgen::prelude::*;
use serde::Serialize;

use object::{Object, ObjectSection};
use gimli::{
    Dwarf, DwarfSections, EndianSlice, RunTimeEndian, Unit, DebugInfoOffset, AttributeValue, Expression, Operation
};
// Import log macros
use log::{info, warn, error, debug}; // Keep debug for potentially useful high-level info
// Import demangler
use cpp_demangle::{Symbol, DemangleOptions};


const MAX_RECURSION_DEPTH: usize = 15;
const MAX_SIZE_CALC_DEPTH: usize = 10; // Depth for get_type_size helper

// Structure to hold the "flattened" information for each primitive component
#[derive(Serialize, Debug, Clone)]
pub struct BaseVariableInfo {
    name: String,        // Demangled name if C++, original otherwise
    type_name: String,
    address: u64,
    size: u64,
    file_name: Option<String>,
    line_number: Option<u64>,
}

// --- Function to initialize logger and panic hook ---
#[wasm_bindgen(start)]
pub fn start() {
    static START: std::sync::Once = std::sync::Once::new();
    START.call_once(|| {
        console_error_panic_hook::set_once();
        // Set default log level to Info for production
        wasm_logger::init(wasm_logger::Config::new(log::Level::Info));
        info!("Wasm module initialized, logger ready.");
    });
}


// Helper to load DWARF sections
fn load_section<'data>(
    obj_file: &'data object::File<'data>,
    id: gimli::SectionId,
) -> Result<EndianSlice<'data, RunTimeEndian>, gimli::Error> {
    let data = obj_file
        .section_by_name(id.name())
        .and_then(|section| section.data().ok())
        .unwrap_or(&[]);
    let endian = if obj_file.is_little_endian() { RunTimeEndian::Little } else { RunTimeEndian::Big };
    Ok(EndianSlice::new(data, endian))
}

// Helper function to get the byte size of a type DIE
fn get_type_size(
    dwarf: &Dwarf<EndianSlice<RunTimeEndian>>,
    unit: &Unit<EndianSlice<RunTimeEndian>, usize>,
    type_offset: DebugInfoOffset,
    depth: usize,
) -> Option<u64> {
    if depth > MAX_SIZE_CALC_DEPTH { return None; }

    let unit_offset = type_offset.to_unit_offset(&unit.header)?;
    let die = unit.entry(unit_offset).ok()?;

    if let Some(size) = die.attr_value(gimli::DW_AT_byte_size).ok().flatten().and_then(|a| a.udata_value()) {
        if size > 0 { return Some(size); }
    }

    match die.tag() {
        gimli::DW_TAG_pointer_type | gimli::DW_TAG_reference_type => Some(unit.header.address_size() as u64),
        gimli::DW_TAG_typedef | gimli::DW_TAG_const_type | gimli::DW_TAG_volatile_type | gimli::DW_TAG_restrict_type => {
            let underlying_type_attr = die.attr_value(gimli::DW_AT_type).ok().flatten()?;
            match underlying_type_attr {
                AttributeValue::UnitRef(offset) => {
                    let underlying_dio = offset.to_debug_info_offset(&unit.header)?;
                    get_type_size(dwarf, unit, underlying_dio, depth + 1)
                }
                _ => None,
            }
        }
        gimli::DW_TAG_enumeration_type => {
             if let Some(AttributeValue::UnitRef(enum_underlying_type_ref)) = die.attr_value(gimli::DW_AT_type).ok().flatten() {
                if let Some(enum_underlying_dio) = enum_underlying_type_ref.to_debug_info_offset(&unit.header){
                    return get_type_size(dwarf, unit, enum_underlying_dio, depth + 1);
                }
            }
            // Fallback to DW_AT_byte_size if enum has no explicit underlying type ref but has size
            die.attr_value(gimli::DW_AT_byte_size).ok().flatten().and_then(|a| a.udata_value())
        }
        _ => None,
    }
}


#[wasm_bindgen]
pub fn analyze_elf_recursively(elf_bytes: &[u8]) -> Result<JsValue, JsValue> {
    let mut results: Vec<BaseVariableInfo> = Vec::new();
    info!("Starting DWARF-centric recursive ELF analysis for {} bytes.", elf_bytes.len());

    let obj_file = match object::File::parse(elf_bytes) {
        Ok(file) => file,
        Err(e) => {
            error!("Failed to parse ELF file: {}", e);
            return Err(JsValue::from_str(&format!("Failed to parse ELF file: {}", e)));
        }
    };

    let sections = DwarfSections::load(|id| load_section(&obj_file, id))
        .map_err(|e| {
            error!("Failed to load DWARF sections: {}", e);
            JsValue::from_str(&format!("Failed to load DWARF sections: {}", e))
        })?;

    let dwarf = sections.borrow(|section| {
        gimli::EndianSlice::new(section, if obj_file.is_little_endian() { RunTimeEndian::Little } else { RunTimeEndian::Big })
    });

    let mut iter = dwarf.units();
    while let Some(header) = iter.next().unwrap_or(None) {
        let unit = match dwarf.unit(header.clone()) {
            Ok(u) => u,
            Err(_e) => {
                warn!("Failed to parse DWARF unit at offset {:?}: {:?}", header.offset(), _e);
                continue;
            }
        };

        let mut tree = match unit.entries_tree(None) { Ok(t) => t, Err(_) => continue };
        let root_node = tree.root().unwrap();

        let mut cursor = root_node.children();
        while let Some(child_node) = cursor.next().unwrap_or(None) {
            process_die_node_for_variables(child_node, &dwarf, &unit, &mut results);
        }
    }

    info!("Finished analysis. Found {} primitive components.", results.len());
    results.sort_by(|a, b| a.name.cmp(&b.name));
    serde_wasm_bindgen::to_value(&results)
        .map_err(|e| JsValue::from_str(&format!("Serialization error: {}", e)))
}

fn process_die_node_for_variables<'abbrev, 'unit, 'tree, 'data>(
    node: gimli::EntriesTreeNode<'abbrev, 'unit, 'tree, EndianSlice<'data, RunTimeEndian>>,
    dwarf: &Dwarf<EndianSlice<'data, RunTimeEndian>>,
    unit: &'unit Unit<EndianSlice<'data, RunTimeEndian>, usize>,
    results: &mut Vec<BaseVariableInfo>,
) {
    let die = node.entry();

    if die.tag() == gimli::DW_TAG_variable {
        let location_attr_opt = die.attr_value(gimli::DW_AT_location).ok().flatten();
        let declaration_flag = die.attr_value(gimli::DW_AT_declaration).ok().flatten()
            .map_or(false, |attr| matches!(attr, AttributeValue::Flag(true)));
        let specification_attr_opt = die.attr_value(gimli::DW_AT_specification).ok().flatten();

        if location_attr_opt.is_none() && specification_attr_opt.is_none() {
            if declaration_flag { /* Pure declaration, skip direct processing */ }
            // Still process children for nested variables
            let mut children_cursor = node.children();
            while let Some(child_node) = children_cursor.next().unwrap_or(None) {
                process_die_node_for_variables(child_node, dwarf, unit, results);
            }
            return;
        }
        
        let mut name_av_opt: Option<AttributeValue<EndianSlice<RunTimeEndian>, usize>> = None;
        let mut type_attr_opt: Option<AttributeValue<EndianSlice<RunTimeEndian>, usize>> = None;
        let mut decl_file_attr_opt: Option<AttributeValue<EndianSlice<RunTimeEndian>, usize>> = None;
        let mut decl_line_attr_opt: Option<AttributeValue<EndianSlice<RunTimeEndian>, usize>> = None;

        if let Some(AttributeValue::UnitRef(spec_offset)) = specification_attr_opt {
            if let Ok(spec_die) = unit.entry(spec_offset) {
                name_av_opt = spec_die.attr_value(gimli::DW_AT_linkage_name).ok().flatten()
                    .or_else(|| spec_die.attr_value(gimli::DW_AT_MIPS_linkage_name).ok().flatten())
                    .or_else(|| spec_die.attr_value(gimli::DW_AT_name).ok().flatten());
                type_attr_opt = spec_die.attr_value(gimli::DW_AT_type).ok().flatten();
                decl_file_attr_opt = spec_die.attr_value(gimli::DW_AT_decl_file).ok().flatten();
                decl_line_attr_opt = spec_die.attr_value(gimli::DW_AT_decl_line).ok().flatten();
            } else {
                 warn!("Failed to lookup specification DIE at {:?}", spec_offset);
            }
        } else {
            name_av_opt = die.attr_value(gimli::DW_AT_linkage_name).ok().flatten()
                .or_else(|| die.attr_value(gimli::DW_AT_MIPS_linkage_name).ok().flatten())
                .or_else(|| die.attr_value(gimli::DW_AT_name).ok().flatten());
            type_attr_opt = die.attr_value(gimli::DW_AT_type).ok().flatten();
            decl_file_attr_opt = die.attr_value(gimli::DW_AT_decl_file).ok().flatten();
            decl_line_attr_opt = die.attr_value(gimli::DW_AT_decl_line).ok().flatten();
        }

        if let (Some(name_attribute_value), Some(AttributeValue::UnitRef(type_unit_offset)), Some(loc_av_val)) = (name_av_opt, type_attr_opt, location_attr_opt) {
            let raw_var_name = match dwarf.attr_string(unit, name_attribute_value) {
                 Ok(name_slice) => name_slice.to_string_lossy().into_owned(),
                 Err(_) => format!("<unnamed_var_offset_{:?}>", die.offset().0),
            };

            let demangled_name = match Symbol::new(raw_var_name.as_bytes()) {
                Ok(sym) => sym.demangle(&DemangleOptions::default()).unwrap_or_else(|_| raw_var_name.clone()),
                Err(_) => raw_var_name.clone(),
            };
            let var_name = demangled_name;

            if raw_var_name != var_name {
                debug!("Demangled '{}' -> '{}'", raw_var_name, var_name); // Keep this debug for C++
            }

            let type_debug_info_offset = match type_unit_offset.to_debug_info_offset(&unit.header) {
                Some(dio) => dio,
                None => { warn!("Variable '{}' has invalid type offset. Skipping.", var_name); return; }
            };

            let mut file_name: Option<String> = None;
            let mut line_number: Option<u64> = None;

            if let Some(line_attr_val) = decl_line_attr_opt {
                line_number = line_attr_val.udata_value();
            }

            let file_index_opt: Option<u64> = match decl_file_attr_opt {
                Some(AttributeValue::FileIndex(val)) => Some(val),
                Some(AttributeValue::Udata(val)) => Some(val),
                Some(AttributeValue::Sdata(val)) => Some(val as u64),
                Some(AttributeValue::Data1(val)) => Some(val as u64),
                Some(AttributeValue::Data2(val)) => Some(val as u64),
                Some(AttributeValue::Data4(val)) => Some(val as u64),
                Some(AttributeValue::Data8(val)) => Some(val),
                _ => None,
            };

            if let Some(file_index) = file_index_opt {
                if let Some(line_program) = unit.line_program.as_ref() {
                     let lp_header = line_program.header();
                     if file_index > 0 && file_index as usize <= lp_header.file_names().len() {
                         if let Some(file_entry) = lp_header.file(file_index) {
                            let mut path_str = String::new();
                            let dir_index = file_entry.directory_index();
                            if dir_index != 0 {
                                if let Some(dir_av) = lp_header.directory(dir_index) {
                                    if let Ok(dir_s) = dwarf.attr_string(unit, dir_av.clone()) { 
                                        let dir_part = dir_s.to_string_lossy();
                                        if !dir_part.is_empty() { path_str.push_str(&dir_part); if !dir_part.ends_with('/') {path_str.push('/');} }
                                    }
                                }
                            }
                            if let Ok(file_s) = dwarf.attr_string(unit, file_entry.path_name()) { path_str.push_str(&file_s.to_string_lossy());}

                            if !path_str.is_empty() { file_name = Some(path_str); }
                         }
                     }
                }
            }


            let mut var_address: Option<u64> = None;
            if let AttributeValue::Exprloc(expr) = loc_av_val {
                var_address = evaluate_simple_address_expr(expr, unit.encoding());
            } else if let AttributeValue::LocationListsRef(_offset) = loc_av_val {
                 // Location lists are complex, not handled for simplicity
            }


            if let Some(address) = var_address {
                walk_type_die(
                    dwarf, unit, type_debug_info_offset,
                    var_name, address, results, 0,
                    file_name, line_number
                );
            } else {
                 warn!("Variable '{}': Could not determine static address. Skipping.", var_name);
            }
        }
    }

    let mut children_cursor = node.children();
    while let Some(child_node) = children_cursor.next().unwrap_or(None) {
        process_die_node_for_variables(child_node, dwarf, unit, results);
    }
}

fn evaluate_simple_address_expr(expr: Expression<EndianSlice<RunTimeEndian>>, encoding: gimli::Encoding) -> Option<u64> {
    let mut ops_iter = expr.operations(encoding);
    match ops_iter.next() {
        Ok(Some(Operation::Address { address })) => {
            if ops_iter.next().unwrap_or(None).is_none() { return Some(address); }
        }
        _ => {}
    }
    None
}

fn walk_type_die<'data>(
    dwarf: &Dwarf<EndianSlice<'data, RunTimeEndian>>,
    unit: &Unit<EndianSlice<'data, RunTimeEndian>, usize>,
    type_offset: DebugInfoOffset,
    current_path: String,
    current_address: u64,
    results: &mut Vec<BaseVariableInfo>,
    depth: usize,
    decl_file_name: Option<String>,
    decl_line_number: Option<u64>,
) {
    if depth > MAX_RECURSION_DEPTH {
        warn!("Max recursion depth reached for path: {}", current_path);
        results.push(BaseVariableInfo { name: format!("{}.<max_depth>", current_path), type_name: "RECURSION_LIMIT".into(), address: current_address, size: 0, file_name: decl_file_name.clone(), line_number: decl_line_number });
        return;
    }

    let unit_offset = match type_offset.to_unit_offset(&unit.header) { Some(uo) => uo, None => { /* warn! for path */ return; } };
    let type_die = match unit.entry(unit_offset) { Ok(die) => die, Err(_) => { /* error! for path */ return; } };

    let type_name_attr_val = type_die.attr_value(gimli::DW_AT_name).ok().flatten();
    let type_name_str = type_name_attr_val
        .and_then(|val| dwarf.attr_string(unit, val).ok())
        .map(|s| s.to_string_lossy().into_owned());

    let mut actual_byte_size = type_die.attr_value(gimli::DW_AT_byte_size)
        .ok().flatten().and_then(|a| a.udata_value());

    if actual_byte_size.is_none() || actual_byte_size == Some(0) {
        actual_byte_size = get_type_size(dwarf, unit, type_offset, 0);
    }
    let type_byte_size = actual_byte_size.unwrap_or(0);


    match type_die.tag() {
        gimli::DW_TAG_base_type => {
            results.push(BaseVariableInfo {
                name: current_path,
                type_name: type_name_str.unwrap_or_else(|| "base_type".into()),
                address: current_address, size: type_byte_size,
                file_name: decl_file_name, line_number: decl_line_number,
            });
        }
        gimli::DW_TAG_pointer_type | gimli::DW_TAG_reference_type => {
            results.push(BaseVariableInfo {
                name: current_path,
                type_name: type_name_str.unwrap_or_else(|| if type_die.tag() == gimli::DW_TAG_pointer_type {"pointer".into()} else {"reference".into()}),
                address: current_address, size: unit.header.address_size() as u64,
                file_name: decl_file_name, line_number: decl_line_number,
            });
        }
        gimli::DW_TAG_array_type => {
            let element_type_attr_opt = type_die.attr_value(gimli::DW_AT_type).ok().flatten();
            let element_type_offset_ref = match element_type_attr_opt { Some(AttributeValue::UnitRef(offset)) => offset, _ => return };
            let element_type_dio = match element_type_offset_ref.to_debug_info_offset(&unit.header) { Some(dio) => dio, _ => return };

            let element_byte_size = get_type_size(dwarf, unit, element_type_dio, 0).unwrap_or(0);
            if element_byte_size == 0 { return; }

            let mut total_elements = 0;
            let mut tree = unit.entries_tree(Some(type_die.offset())).unwrap_or_else(|_| unit.entries_tree(None).unwrap());
            let mut children = tree.root().unwrap().children();
            while let Some(child_node) = children.next().unwrap_or(None) {
                let child = child_node.entry();
                if child.tag() == gimli::DW_TAG_subrange_type {
                    if let Some(count) = child.attr_value(gimli::DW_AT_count).ok().flatten().and_then(|a| a.udata_value()) {
                        total_elements = count; break;
                    }
                    if let Some(upper_bound) = child.attr_value(gimli::DW_AT_upper_bound).ok().flatten().and_then(|a| a.udata_value()) {
                        let lower_bound = child.attr_value(gimli::DW_AT_lower_bound).ok().flatten().and_then(|a| a.udata_value()).unwrap_or(0);
                        total_elements = upper_bound.saturating_sub(lower_bound) + 1; break;
                    }
                }
            }
            if total_elements == 0 {
                if type_byte_size > 0 { total_elements = type_byte_size / element_byte_size; }
                else { return; }
            }
            if total_elements == 0 { return; }

            for i in 0..total_elements {
                walk_type_die(
                    dwarf, unit, element_type_dio,
                    format!("{}[{}]", current_path, i),
                    current_address + (i * element_byte_size),
                    results, depth + 1,
                    decl_file_name.clone(), decl_line_number,
                );
            }
        }
        gimli::DW_TAG_structure_type | gimli::DW_TAG_union_type | gimli::DW_TAG_class_type => {
            let name = type_name_str.unwrap_or_else(|| "anonymous_aggregate".into());
            let is_declaration = type_die.attr_value(gimli::DW_AT_declaration).ok().flatten()
                .map_or(false, |attr| matches!(attr, AttributeValue::Flag(true)));

            if is_declaration && type_byte_size == 0 {
                results.push(BaseVariableInfo { name: current_path, type_name: format!("incomplete {}", name), address: current_address, size: 0, file_name: decl_file_name.clone(), line_number: decl_line_number });
                return;
            }

            let mut tree = unit.entries_tree(Some(type_die.offset())).unwrap_or_else(|_| unit.entries_tree(None).unwrap());
            let mut children = tree.root().unwrap().children();
            let mut has_members = false;
            while let Some(child_node) = children.next().unwrap_or(None) {
                let member_die = child_node.entry();
                if member_die.tag() == gimli::DW_TAG_member {
                    has_members = true;
                    let member_name_attr_opt = member_die.attr_value(gimli::DW_AT_name).ok().flatten();
                    let member_name = member_name_attr_opt
                        .and_then(|val| dwarf.attr_string(unit, val).ok())
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| format!("<anon_member_offset_{:?}>", member_die.offset().0));

                    let member_type_attr_opt = member_die.attr_value(gimli::DW_AT_type).ok().flatten();
                    let member_type_offset_ref = match member_type_attr_opt { Some(AttributeValue::UnitRef(offset)) => offset, _ => continue };
                    let member_type_dio = match member_type_offset_ref.to_debug_info_offset(&unit.header) { Some(dio) => dio, _ => continue };

                    let member_offset_in_parent = member_die.attr_value(gimli::DW_AT_data_member_location).ok().flatten()
                        .and_then(|val| match val {
                            AttributeValue::Udata(offset) => Some(offset),
                            AttributeValue::Sdata(offset) => Some(offset as u64),
                            _ => None,
                        }).unwrap_or(0);

                    walk_type_die(
                        dwarf, unit, member_type_dio,
                        format!("{}.{}", current_path, member_name),
                        current_address + member_offset_in_parent,
                        results, depth + 1,
                        decl_file_name.clone(), decl_line_number,
                    );
                }
            }
            if !has_members && type_byte_size > 0 {
                 results.push(BaseVariableInfo {
                    name: current_path, type_name: name, address: current_address,
                    size: type_byte_size, file_name: decl_file_name.clone(), line_number: decl_line_number,
                });
            }
        }
        gimli::DW_TAG_typedef => {
            if let Some(AttributeValue::UnitRef(actual_type_offset_ref)) = type_die.attr_value(gimli::DW_AT_type).ok().flatten() {
                 if let Some(actual_type_dio) = actual_type_offset_ref.to_debug_info_offset(&unit.header) {
                    walk_type_die(dwarf, unit, actual_type_dio, current_path, current_address, results, depth, decl_file_name, decl_line_number);
                } else {
                     results.push(BaseVariableInfo { name: current_path, type_name: format!("unresolved_typedef_{}", type_name_str.unwrap_or_default()), address: current_address, size: 0, file_name: decl_file_name.clone(), line_number: decl_line_number });
                }
            } else {
                results.push(BaseVariableInfo { name: current_path, type_name: format!("unresolved_typedef_{}", type_name_str.unwrap_or_default()), address: current_address, size: 0, file_name: decl_file_name.clone(), line_number: decl_line_number });
            }
        }
        gimli::DW_TAG_enumeration_type => {
            results.push(BaseVariableInfo {
                name: current_path,
                type_name: type_name_str.unwrap_or_else(|| "enum".into()),
                address: current_address, size: type_byte_size,
                file_name: decl_file_name.clone(), line_number: decl_line_number,
            });
        }
        gimli::DW_TAG_const_type | gimli::DW_TAG_volatile_type | gimli::DW_TAG_restrict_type => {
             if let Some(AttributeValue::UnitRef(actual_type_offset_ref)) = type_die.attr_value(gimli::DW_AT_type).ok().flatten() {
                 if let Some(actual_type_dio) = actual_type_offset_ref.to_debug_info_offset(&unit.header) {
                    walk_type_die(dwarf, unit, actual_type_dio, current_path, current_address, results, depth, decl_file_name, decl_line_number);
                }
            }
        }
        _ => { 
            results.push(BaseVariableInfo {
                name: current_path,
                type_name: type_name_str.unwrap_or_else(||format!("{:?}", type_die.tag())),
                address: current_address, size: type_byte_size,
                file_name: decl_file_name.clone(), line_number: decl_line_number,
            });
        }
    }
}
