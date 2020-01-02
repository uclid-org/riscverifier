use object::Object;
use std::collections::BTreeMap;
use std::convert::TryInto;
use std::{borrow, fs};

#[derive(Debug, Clone)]
pub struct FunctionSig {
    // TODO: Use references instead of vecs? otherwise we need to clone this
    pub in_types: Vec<(String, u64)>,
    pub out_type: u64,
}

#[derive(Debug)]
pub struct GlobalVariable {
    name: String,
    byte_size: u64,
    memory_addr: u64,
}

#[derive(Debug)]
pub struct DwarfReader {
    dwarf_objects: Vec<DwarfObject>,
}

#[derive(Debug)]
pub struct DwarfObject {
    tag_name: String,
    offset: usize,
    attrs: BTreeMap<String, DwarfAttributeValue>,
    child_tags: BTreeMap<usize, DwarfObject>,
}

#[derive(Debug)]
pub enum DwarfAttributeValue {
    NumericAttr(u64),
    StringAttr(String),
    BooleanAttr(bool),
}

impl DwarfObject {
    pub fn create(
        tag_name: String,
        offset: usize,
        attrs: BTreeMap<String, DwarfAttributeValue>,
        child_tags: BTreeMap<usize, DwarfObject>,
    ) -> DwarfObject {
        DwarfObject {
            tag_name,
            offset,
            attrs,
            child_tags,
        }
    }

    pub fn add_child_tag(&mut self, dwarf_object: DwarfObject) {
        self.child_tags.insert(dwarf_object.offset, dwarf_object);
    }

    pub fn last_child(&mut self) -> DwarfObject {
        let last_child_key = self.child_tags.values_mut().last().unwrap().offset;
        self.child_tags.remove(&last_child_key).unwrap()
    }
}

impl DwarfReader {
    pub fn create(files: &Vec<String>) -> DwarfReader {
        DwarfReader {
            dwarf_objects: DwarfReader::process_dwarf_files(files)
                .expect("Encountered error while parsing binary files."),
        }
    }

    pub fn get_function_signature(&self, function_name: &str) -> FunctionSig {
        let comp_unit = self
            .dwarf_objects
            .iter()
            .find(|dwarf_object| {
                dwarf_object
                    .child_tags
                    .iter()
                    .find(|(_, dwarf_object2)| {
                        let dw_at_name = &dwarf_object2.attrs.get("DW_AT_name");
                        &dwarf_object2.tag_name == "DW_TAG_subprogram"
                            && !dw_at_name.is_none()
                            && match dw_at_name.unwrap() {
                                DwarfAttributeValue::StringAttr(name) => name == function_name,
                                _ => panic!("Could not find function."),
                            }
                    })
                    .is_some()
            })
            .expect("[get_function_signature] No dwarf objects...");
        // debug!("comp_unit: {:#?}", comp_unit);
        let (_offset, dwarf_object) = comp_unit
            .child_tags
            .iter()
            .find(|dwarf_object| {
                let dw_at_name = &dwarf_object.1.attrs.get("DW_AT_name");
                &dwarf_object.1.tag_name == "DW_TAG_subprogram"
                    && !dw_at_name.is_none()
                    && match dw_at_name.unwrap() {
                        DwarfAttributeValue::StringAttr(name) => name == function_name,
                        _ => false,
                    }
            })
            .expect("[get_function_signature] Could not find function.");
        let in_types = dwarf_object
            .child_tags
            .iter()
            .filter(|(_offset, child)| child.tag_name == "DW_TAG_formal_parameter")
            .map(|(_offset, child)| {
                // debug!("[get_function_signature] Found formal for {}: {:#?}", function_name, child);
                let formal_name = match child
                    .attrs
                    .get("DW_AT_name")
                    .expect("[get_function_signature] Formal does not have name.")
                {
                    DwarfAttributeValue::StringAttr(name) => name.clone(),
                    _ => panic!("[get_function_signature] Name should be a string!"),
                };
                let formal_size_index = match child
                    .attrs
                    .get("DW_AT_type")
                    .expect("[get_function_signature] Formal does not have size.")
                {
                    DwarfAttributeValue::NumericAttr(value) => value.clone(),
                    _ => panic!(
                        "[get_function_signature] Formal size index should be a numeric value."
                    ),
                };
                // debug!("formal_size_index: {:#?}", formal_size_index);
                let formal_size = self.get_type_size(&(formal_size_index as usize), comp_unit);
                (formal_name, formal_size)
            })
            .collect();
        let out_type = match dwarf_object.attrs.get("DW_AT_type") {
            Some(dwarf_attr) => match dwarf_attr {
                DwarfAttributeValue::NumericAttr(value) => {
                    self.get_type_size(&(*value as usize), comp_unit)
                }
                _ => panic!("[get_function_signature] Type should be numeric."),
            },
            _ => 0,
        };
        FunctionSig { in_types, out_type }
    }

    fn get_type_size(&self, dwarf_object_index: &usize, comp_unit: &DwarfObject) -> u64 {
        let dwarf_object = comp_unit
            .child_tags
            .get(dwarf_object_index)
            .unwrap_or_else(|| {
                panic!(
                    "[get_type_size] No such node at address {}.",
                    dwarf_object_index
                )
            });
        match &dwarf_object.tag_name[..] {
            "DW_TAG_typedef" => {
                let next_type_index = match dwarf_object.attrs
                        .get(&"DW_AT_type".to_string())
                        .unwrap_or_else(|| panic!("[get_type_size] Type definition at address {} didn't have a DW_AT_type tag.", dwarf_object.offset))
                        {
                            DwarfAttributeValue::NumericAttr(value) => value.clone(),
                            _=> panic!("[get_type_size] Should be numeric index."),
                        };
                self.get_type_size(&(next_type_index as usize), comp_unit)
            }
            "DW_TAG_base_type" => {
                match dwarf_object.attrs.get(&"DW_AT_byte_size".to_string())
                .unwrap_or_else(|| panic!("[get_type_size] No DW_AT_byte_size tag inside base type at address {}.", dwarf_object.offset)) {
                    DwarfAttributeValue::NumericAttr(value) => value.clone(),
                    _ => panic!("[get_type_size] DW_AT_byte_size should be a numeric value."),
                }
            }
            _ => panic!("[get_type_size] Not a type dwarf object!"),
        }
    }

    // Returns a list of global variables with their names and memory locations
    pub fn get_global_variables(&self) -> Vec<GlobalVariable> {
        vec![]
    }

    fn process_dwarf_files(files: &Vec<String>) -> Result<Vec<DwarfObject>, gimli::Error> {
        let mut dwarf_objects = vec![];
        for path in files {
            info!("[process_dwarf_files] Processing dwarf file {:?}.", path);
            let file = fs::File::open(&path[..]).unwrap();
            let mmap = unsafe { memmap::Mmap::map(&file).unwrap() };
            let object = object::File::parse(&*mmap).unwrap();
            let endian = if object.is_little_endian() {
                gimli::RunTimeEndian::Little
            } else {
                gimli::RunTimeEndian::Big
            };
            let mut file_objects = DwarfReader::process_dwarf_file(&object, endian)?;
            // debug!("file_objects: {:#?}", file_objects);
            dwarf_objects.append(&mut file_objects);
        }
        // debug!("{:#?}", dwarf_objects);
        Ok(dwarf_objects)
    }

    fn process_dwarf_file(
        object: &object::File,
        endian: gimli::RunTimeEndian,
    ) -> Result<Vec<DwarfObject>, gimli::Error> {
        // Load a section and return as `Cow<[u8]>`.
        let load_section = |id: gimli::SectionId| -> Result<borrow::Cow<[u8]>, gimli::Error> {
            Ok(object
                .section_data_by_name(id.name())
                .unwrap_or(borrow::Cow::Borrowed(&[][..])))
        };
        // Load a supplementary section. We don't have a supplementary object file,
        // so always return an empty slice.
        let load_section_sup = |_| Ok(borrow::Cow::Borrowed(&[][..]));
        // Load all of the sections.
        let dwarf_cow = gimli::Dwarf::load(&load_section, &load_section_sup)?;
        // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
        let borrow_section: &dyn for<'a> Fn(
            &'a borrow::Cow<[u8]>,
        )
            -> gimli::EndianSlice<'a, gimli::RunTimeEndian> =
            &|section| gimli::EndianSlice::new(&*section, endian);
        // Create `EndianSlice`s for all of the sections.
        let dwarf = dwarf_cow.borrow(&borrow_section);
        // Iterate over the compilation units.
        let mut iter = dwarf.units();
        let mut dwarf_objects = vec![];
        while let Some(header) = iter.next()? {
            // debug!(
            //     "[process_dwarf_file] Processing unit at <.debug_info+0x{:x}>",
            //     header.offset().0
            // );
            let unit = dwarf.unit(header)?;
            // Iterate over the Debugging Information Entries (DIEs) in the unit.
            let mut entries_cursor = unit.entries();
            if let Some(dwarf_object) =
                DwarfReader::entries_to_dwarf_object(&dwarf, &mut entries_cursor)?
            {
                // info!("Compilation unit: \n{:#?}", &dwarf_object);
                dwarf_objects.push(dwarf_object);
            }
        }
        Ok(dwarf_objects)
    }

    fn print_gimli_dwarf<R: gimli::Reader<Offset = usize>>(
        dwarf: &gimli::Dwarf<R>,
        entries_cursor: &mut gimli::EntriesCursor<R>,
    ) -> Result<(), gimli::Error> {
        let mut depth = 0;
        while let Some((delta_depth, entry)) = entries_cursor.next_dfs()? {
            let tag_name = entry.tag().to_string();
            depth += delta_depth;
            // info!(
            //     "[print_gimli_dwarf] Depth: {} -- Offset {:x} -- Processing {} ==============",
            //     depth,
            //     entry.offset().0,
            //     tag_name
            // );
            // Iterate over the attributes in the DIE.
            let mut attrs_cursor = entry.attrs();
            while let Some(attr) = attrs_cursor.next()? {
                let attr_name = attr.name().to_string();
                let attr_value = DwarfReader::get_attr_value(&attr, dwarf)?;
                // info!(
                //     "[print_gimli_dwarf] {}{}: {:?}",
                //     "   ".repeat(depth.try_into().unwrap()),
                //     &attr_name,
                //     &attr_value
                // );
            }
        }
        Ok(())
    }

    fn entries_to_dwarf_object<R: gimli::Reader<Offset = usize>>(
        dwarf: &gimli::Dwarf<R>,
        entries_cursor: &mut gimli::EntriesCursor<R>,
    ) -> Result<Option<DwarfObject>, gimli::Error> {
        if let Some((_, entry)) = entries_cursor.next_dfs()? {
            // Stack of predecessor dwarf objects for recursive construction
            let mut dwarf_object_stack: Vec<DwarfObject> = vec![];
            // Immediate parent of the processed node
            let mut parent;
            // debug!(
            //     "[gimli_unit_to_dwarf_object] Processing the first node... {}",
            //     entry.tag().to_string()
            // );
            // Create dummy node to store unit
            let first_dwarf_object = DwarfObject::create(
                entry.tag().to_string(),
                entry.offset().0,
                DwarfReader::gimli_attr_to_dwarf_attr_map(entry, dwarf)?,
                BTreeMap::new(),
            );
            parent = DwarfObject::create(format!("dummy"), 0, BTreeMap::new(), BTreeMap::new());
            parent.add_child_tag(first_dwarf_object);
            // DFS traverse through the remaining nodes
            while let Some((delta_depth, entry)) = entries_cursor.next_dfs()? {
                // debug!(
                //     "[gimli_unit_to_dwarf_object] Processing next node... <{}> {}",
                //     delta_depth,
                //     entry.tag().to_string()
                // );
                match delta_depth {
                    // If increasing depth, then extract the parent from the current parent's last child
                    _ if delta_depth > 0 => {
                        assert!(delta_depth == 1, "Depth of DWARF node increased by more than 1! Probably an ill-formed DWARF format.");
                        let mut grandparent = parent;
                        parent = grandparent.last_child();
                        dwarf_object_stack.push(grandparent);
                    }
                    // If depth decreases, then add parent back to the grandparent recursively
                    _ if delta_depth < 0 => {
                        for _ in 0..-delta_depth {
                            let mut grandparent = dwarf_object_stack.pop().unwrap();
                            grandparent.add_child_tag(parent);
                            parent = grandparent;
                        }
                    }
                    // If depth doesn't increase, just add the node to the parent
                    _ => (),
                }
                parent.add_child_tag(DwarfObject::create(
                    entry.tag().to_string(),
                    entry.offset().0,
                    DwarfReader::gimli_attr_to_dwarf_attr_map(entry, dwarf)?,
                    BTreeMap::new(),
                ));
            }
            // Recursively add parent to grandparent until one node remains (dummy node in the stack and parent is the actual node to return)
            while dwarf_object_stack.len() > 1 {
                let mut grandparent = dwarf_object_stack.pop().unwrap();
                grandparent.add_child_tag(parent);
                parent = grandparent;
            }
            // info!("[entries_to_dwarf_object] DWARF object generated for file.");
            return Ok(Some(parent));
        }
        // warn!("[entries_to_dwarf_object] No DWARF objects generated for file.");
        Ok(None)
    }

    fn gimli_attr_to_dwarf_attr_map<R: gimli::Reader<Offset = usize>>(
        entry: &gimli::DebuggingInformationEntry<R>,
        dwarf: &gimli::Dwarf<R>,
    ) -> Result<BTreeMap<String, DwarfAttributeValue>, gimli::Error> {
        let mut attributes = BTreeMap::new();
        let mut attrs_cursor = entry.attrs();
        while let Some(attr) = attrs_cursor.next()? {
            if let Some(attr_value) = DwarfReader::get_attr_value(&attr, dwarf)? {
                attributes.insert(attr.name().to_string(), attr_value);
            }
        }
        Ok(attributes)
    }

    fn get_attr_value<R: gimli::Reader<Offset = usize>>(
        attr: &gimli::Attribute<R>,
        dwarf: &gimli::Dwarf<R>,
    ) -> Result<Option<DwarfAttributeValue>, gimli::Error> {
        let value = attr.value();
        let attr_value = match value {
            gimli::AttributeValue::String(s) => Some(DwarfAttributeValue::StringAttr(format!(
                "{}",
                s.to_string_lossy()?
            ))),
            gimli::AttributeValue::DebugStrRef(offset) => {
                let s = dwarf.debug_str.get_str(offset)?;
                Some(DwarfAttributeValue::StringAttr(format!(
                    "{}",
                    s.to_string_lossy()?
                )))
            }
            gimli::AttributeValue::Udata(data) => Some(DwarfAttributeValue::NumericAttr(data)),
            gimli::AttributeValue::UnitRef(offset) => {
                Some(DwarfAttributeValue::NumericAttr(offset.0 as u64))
            }
            gimli::AttributeValue::Flag(true) => Some(DwarfAttributeValue::BooleanAttr(true)),
            gimli::AttributeValue::Flag(false) => Some(DwarfAttributeValue::BooleanAttr(false)),
            _ => {
                // info!(
                //     "[get_attr_value] Could not extract attribute value: {:#?}.",
                //     attr.value()
                // );
                None
            }
        };
        Ok(attr_value)
    }
}
