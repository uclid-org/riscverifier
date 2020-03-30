use std::collections::HashMap;
use std::{cell::RefCell, rc::Rc};

use crate::readers::dwarfreader::*;
use crate::utils;

#[derive(Debug)]
pub struct CDwarfInterface;

impl CDwarfInterface {
    /// Converts a DwarfObject to a DwarfFuncSig if it's a function tag.
    fn dobj_to_func_sig(
        dobj: &DwarfObject,
        comp_unit: &DwarfObject,
    ) -> Result<DwarfFuncSig, utils::Error> {
        assert!(dobj.tag_name == "DW_TAG_subprogram");
        let name = dobj.get_attr("DW_AT_name")?.get_expect_str_val().clone();
        let type_defn_index = dobj.get_attr("DW_AT_type")?.get_expect_num_val();
        let type_defn = Self::get_type(type_defn_index, comp_unit).ok();
        let args = dobj
            .child_tags
            .iter()
            .filter(|(_os, child_dobj)| child_dobj.tag_name == "DW_TAG_formal_parameter")
            .map(|(_os, child_dobj)| {
                let formal_name = child_dobj
                    .get_attr("DW_AT_name")?
                    .get_expect_str_val()
                    .clone();
                let formal_type_index = child_dobj.get_attr("DW_AT_type")?.get_expect_num_val();
                let formal_type = Self::get_type(formal_type_index, comp_unit)?;
                Ok(DwarfVar::new(formal_name, formal_type, 0))
            })
            .filter(|res: &Result<DwarfVar, utils::Error>| res.is_ok())
            .map(|res| res.unwrap())
            .collect::<Vec<_>>();
        Ok(DwarfFuncSig::new(name, args, type_defn))
    }
    /// Converts a DwarfObject to a DwarfVar if it's a variable tag.
    fn dobj_to_var(dobj: &DwarfObject, comp_unit: &DwarfObject) -> Result<DwarfVar, utils::Error> {
        assert!(dobj.tag_name == "DW_TAG_variable");
        let name = dobj.get_attr("DW_AT_name")?.get_expect_str_val().clone();
        let type_defn_index = dobj.get_attr("DW_AT_type")?.get_expect_num_val();
        let type_defn = Self::get_type(type_defn_index, comp_unit)?;
        let memory_addr = *dobj.get_attr("DW_AT_location")?.get_expect_num_val();
        Ok(DwarfVar::new(name, type_defn, memory_addr))
    }
    /// Recursively build the type from comp_unit at dwarf_object_index.
    /// typ_map is used to store the types (to handle mutually recursive)
    /// types.
    fn _get_type(
        dwarf_object_index: &u64,
        comp_unit: &DwarfObject,
        typ_map: &mut HashMap<u64, RefCell<Rc<DwarfTypeDefn>>>,
    ) -> Result<Rc<DwarfTypeDefn>, utils::Error> {
        // Return type if it has been computed
        if let Some(typ) = typ_map.get(dwarf_object_index) {
            return Ok(Rc::clone(&typ.borrow()));
        }
        // Insert dummy (to deal with cyclic types)
        typ_map.insert(
            *dwarf_object_index,
            RefCell::new(Rc::new(DwarfTypeDefn::Primitive { bytes: 0 })),
        );
        // Construct dwarf object type
        let dwarf_object = comp_unit.get_child(dwarf_object_index)?;
        let typ = match &dwarf_object.tag_name[..] {
            "DW_TAG_typedef" | "DW_TAG_volatile_type" => {
                let next_type_index = dwarf_object.get_attr("DW_AT_type")?.get_expect_num_val();
                Self::_get_type(next_type_index, comp_unit, typ_map)?
            }
            // TODO: Check if enumeration type is encoded correctly
            "DW_TAG_base_type" | "DW_TAG_enumeration_type" => {
                let bytes = *dwarf_object
                    .get_attr("DW_AT_byte_size")?
                    .get_expect_num_val();
                assert!(bytes <= 8);
                Rc::new(DwarfTypeDefn::Primitive { bytes })
            }
            "DW_TAG_pointer_type" => {
                let value_typ_index = *dwarf_object.get_attr("DW_AT_type")?.get_expect_num_val();
                let value_typ = Self::_get_type(&value_typ_index, comp_unit, typ_map)?;
                let bytes = *dwarf_object
                    .get_attr("DW_AT_byte_size")?
                    .get_expect_num_val();
                assert!(bytes <= 8);
                Rc::new(DwarfTypeDefn::Pointer { value_typ, bytes })
            }
            "DW_TAG_array_type" => {
                let out_type_index = dwarf_object.get_attr("DW_AT_type")?.get_expect_num_val();
                let out_typ = Self::_get_type(out_type_index, comp_unit, typ_map)?;
                let index_type_index = dwarf_object
                    .get_child_named("DW_TAG_subrange_type")?
                    .get_attr("DW_AT_type")?
                    .get_expect_num_val();
                let in_typ = Self::_get_type(index_type_index, comp_unit, typ_map)?;
                let bytes = *comp_unit.get_attr("pointer_size")?.get_expect_num_val();
                Rc::new(DwarfTypeDefn::Array {
                    in_typ,
                    out_typ,
                    bytes,
                })
            }
            "DW_TAG_structure_type" => {
                let id = dwarf_object
                    .get_attr("DW_AT_name")?
                    .get_expect_str_val()
                    .clone();
                let bytes = *dwarf_object
                    .get_attr("DW_AT_byte_size")?
                    .get_expect_num_val();
                let fields: HashMap<_, _> = dwarf_object
                    .child_tags
                    .iter()
                    .filter(|(_os, child_dobj)| child_dobj.tag_name == "DW_TAG_member")
                    .map(|(_os, child_dobj)| {
                        let field_name = child_dobj.get_attr("DW_AT_name")?.get_expect_str_val();
                        let type_index = child_dobj.get_attr("DW_AT_type")?.get_expect_num_val();
                        let typ = Self::_get_type(type_index, comp_unit, typ_map)?;
                        let loc = *child_dobj
                            .get_attr("DW_AT_data_member_location")?
                            .get_expect_num_val();
                        Ok((
                            field_name.clone(),
                            StructField {
                                name: field_name.clone(),
                                typ,
                                loc,
                            },
                        ))
                    })
                    .filter(|res: &Result<(String, StructField), utils::Error>| res.is_ok())
                    .map(|res| res.unwrap())
                    .collect::<HashMap<String, StructField>>();
                Rc::new(DwarfTypeDefn::Struct { id, fields, bytes })
            }
            _ => return Err(utils::Error::CouldNotFindType),
        };
        match typ_map.get(dwarf_object_index) {
            Some(stub) => {
                stub.replace(Rc::clone(&typ));
            }
            None => {
                typ_map.insert(*dwarf_object_index, RefCell::new(Rc::clone(&typ)));
            }
        }
        Ok(typ)
    }
}

impl DwarfInterface for CDwarfInterface {
    /// Returns a vector of DwarfFuncSig objects from the static (first)
    /// level static functions in comp_unit.
    fn process_func_sigs(comp_unit: &DwarfObject) -> Vec<DwarfFuncSig> {
        let mut func_sigs = vec![];
        for (_child_offset, child_dobj) in &comp_unit.child_tags {
            if &child_dobj.tag_name == "DW_TAG_subprogram" {
                match Self::dobj_to_func_sig(&child_dobj, comp_unit) {
                    Ok(dfs) => func_sigs.push(dfs),
                    Err(_) => (),
                }
            }
        }
        func_sigs
    }
    /// Returns a list of statically defined / global variables
    /// from the first level of comp_unit.
    fn process_global_vars(comp_unit: &DwarfObject) -> Vec<DwarfVar> {
        let mut globals = vec![];
        for (_child_offset, child_dobj) in &comp_unit.child_tags {
            if &child_dobj.tag_name == "DW_TAG_variable" {
                match Self::dobj_to_var(&child_dobj, comp_unit) {
                    Ok(dv) => globals.push(dv),
                    Err(_) => (),
                }
            }
        }
        globals
    }
    /// Returns the type defined at index dwarf_object_index
    /// in the first level of comp_unit.
    fn get_type(
        dwarf_object_index: &u64,
        comp_unit: &DwarfObject,
    ) -> Result<Rc<DwarfTypeDefn>, utils::Error> {
        Self::_get_type(dwarf_object_index, comp_unit, &mut HashMap::new())
    }
}
