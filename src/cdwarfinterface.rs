use std::collections::HashMap;

use crate::dwarfreader::*;
use crate::utils;

#[derive(Debug)]
pub struct CDwarfInterface;

impl CDwarfInterface {
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

    fn dobj_to_var(dobj: &DwarfObject, comp_unit: &DwarfObject) -> Result<DwarfVar, utils::Error> {
        assert!(dobj.tag_name == "DW_TAG_variable");
        let name = dobj.get_attr("DW_AT_name")?.get_expect_str_val().clone();
        let type_defn_index = dobj.get_attr("DW_AT_type")?.get_expect_num_val();
        let type_defn = Self::get_type(type_defn_index, comp_unit)?;
        let memory_addr = *dobj.get_attr("DW_AT_location")?.get_expect_num_val();
        Ok(DwarfVar::new(name, type_defn, memory_addr))
    }
}

impl DwarfInterface for CDwarfInterface {
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

    fn get_type(
        dwarf_object_index: &u64,
        comp_unit: &DwarfObject,
    ) -> Result<DwarfTypeDefn, utils::Error> {
        let dwarf_object = comp_unit.get_child(dwarf_object_index)?;
        match &dwarf_object.tag_name[..] {
            "DW_TAG_typedef" | "DW_TAG_volatile_type" => {
                let next_type_index = dwarf_object.get_attr("DW_AT_type")?.get_expect_num_val();
                Self::get_type(next_type_index, comp_unit)
            }
            "DW_TAG_base_type" | "DW_TAG_enumeration_type" | "DW_TAG_pointer_type" => {
                let bytes = *dwarf_object
                    .get_attr("DW_AT_byte_size")?
                    .get_expect_num_val();
                Ok(DwarfTypeDefn::Primitive { bytes })
            }
            "DW_TAG_array_type" => {
                let out_type_index = dwarf_object.get_attr("DW_AT_type")?.get_expect_num_val();
                let out_typ = Box::new(Self::get_type(out_type_index, comp_unit)?);
                let index_type_index = dwarf_object
                    .get_child_named("DW_TAG_subrange_type")?
                    .get_attr("DW_AT_type")?
                    .get_expect_num_val();
                let in_typ = Box::new(Self::get_type(index_type_index, comp_unit)?);
                Ok(DwarfTypeDefn::Array { in_typ, out_typ })
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
                        let field_name = child_dobj
                            .get_attr("DW_AT_name")
                            .expect("Field doesn't have a name.")
                            .get_expect_str_val();
                        let type_index = child_dobj
                            .get_attr("DW_AT_type")
                            .expect("Field doesn't have a type.")
                            .get_expect_num_val();
                        let typ = Box::new(Self::get_type(type_index, comp_unit).unwrap());
                        let loc = *child_dobj
                            .get_attr("DW_AT_data_member_location")
                            .expect("Field doesn't have a location.")
                            .get_expect_num_val();
                        (
                            field_name.clone(),
                            StructField {
                                name: field_name.clone(),
                                typ,
                                loc,
                            },
                        )
                    })
                    .collect();
                Ok(DwarfTypeDefn::Struct { id, fields, bytes })
            }
            _ => Err(utils::Error::NoSuchDwarfFieldError),
        }
    }
}
