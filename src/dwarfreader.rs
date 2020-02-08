use crate::utils::*;
use object::Object;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::iter::Cloned;
use std::{borrow, cell::RefCell, fs, rc::Rc};

#[derive(Debug, Clone)]
pub struct FunctionSig {
    pub in_types: Vec<(String, u64)>,
    pub out_type: u64,
}

#[derive(Debug)]
pub struct GlobalVariable {
    pub name: String,
    pub size_in_bytes: u64, //FIXME: Remove this
    pub type_defn: Rc<TypeDefinition>,
    pub memory_addr: u64,
    pub is_addr: bool,
}

#[derive(Debug)]
pub struct TypeDefinition {
    pub name: String,
    pub size_in_bytes: u64,
    pub field_decls: Vec<StructFieldDefinition>,
}

#[derive(Debug)]
pub struct StructFieldDefinition {
    pub field_name: String,
    pub field_member_location: u64,
    pub field_size_in_bytes: u64,
}

#[derive(Debug)]
pub enum DwarfAttributeValue {
    NumericAttr(u64),
    StringAttr(String),
    BooleanAttr(bool),
}

#[derive(Debug)]
pub struct DwarfObject {
    tag_name: String,
    offset: usize,
    attrs: BTreeMap<String, DwarfAttributeValue>,
    child_tags: BTreeMap<usize, DwarfObject>,
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

#[derive(Debug)]
pub struct DwarfReader {
    xlen: u64,
    dwarf_objects: Vec<DwarfObject>,
    function_sigs: RefCell<HashMap<String, Rc<FunctionSig>>>,
    global_vars: RefCell<Vec<Rc<GlobalVariable>>>,
    type_declarations: RefCell<HashMap<String, Rc<TypeDefinition>>>,
}

impl DwarfReader {
    pub fn create(xlen: u64, files: &Vec<String>) -> DwarfReader {
        let mut dwarf_reader = DwarfReader {
            xlen,
            dwarf_objects: vec![], // DwarfReader::process_dwarf_files(files).expect("Encountered error while parsing binary files."),
            function_sigs: RefCell::new(HashMap::new()),
            global_vars: RefCell::new(vec![]),
            type_declarations: RefCell::new(HashMap::new()),
        };
        dwarf_reader.process_type_declarations();
        dwarf_reader.process_global_variables();
        dwarf_reader
    }

    /// ========================================================================== ///
    /// Function signature helpers                                                 ///
    /// ========================================================================== ///

    fn process_related_function_signatures(&self, function_name: &str) {
        let comp_unit = self.get_function_comp_unit(function_name);
        self.get_function_signatures(comp_unit);
    }

    fn get_function_comp_unit(&self, function_name: &str) -> &DwarfObject {
        &self
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
            .expect("[get_function_signature] No dwarf objects...")
    }

    fn get_function_signatures(&self, comp_unit: &DwarfObject) {
        for (_child_offset, dwarf_object) in &comp_unit.child_tags {
            // Try to add subprogram if it has all the required fields
            if &dwarf_object.tag_name == "DW_TAG_subprogram" {
                if let Some(dw_at_name) = &dwarf_object.attrs.get("DW_AT_name") {
                    if let DwarfAttributeValue::StringAttr(function_name) = dw_at_name {
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
                                let formal_size = match self.get_type_byte_size(&(formal_size_index as usize), comp_unit) {
                                    Ok(result) => result,
                                    Err(_) => {
                                        warn!("[get_function_signatures] Formal {} in {} has no size.", formal_name, function_name);
                                        0
                                    },
                                };
                                (formal_name, formal_size)
                            })
                            .collect();
                        let out_type = match dwarf_object.attrs.get("DW_AT_type") {
                            Some(dwarf_attr) => match dwarf_attr {
                                DwarfAttributeValue::NumericAttr(value) => {
                                    match self.get_type_byte_size(&(*value as usize), comp_unit) {
                                        Ok(result) => result,
                                        Err(_) => {
                                            // info!("[get_function_signatures] {} has no return type.", function_name);
                                            0
                                        }
                                    }
                                }
                                _ => panic!("[get_function_signature] Type should be numeric."),
                            },
                            _ => 0,
                        };
                        self.function_sigs.borrow_mut().insert(
                            function_name.to_string(),
                            Rc::new(FunctionSig { in_types, out_type }),
                        );
                    }
                }
            }
        }
    }

    pub fn get_function_signature(&self, function_name: &str) -> Rc<FunctionSig> {
        let map_contains_function = self.function_sigs.borrow().contains_key(function_name);
        if map_contains_function {
            Rc::clone(self.function_sigs.borrow().get(function_name).unwrap())
        } else {
            self.process_related_function_signatures(function_name);
            Rc::clone(self.function_sigs.borrow().get(function_name).unwrap())
        }
    }

    /// ========================================================================== ///
    /// Type declaration helpers                                                   ///
    /// ========================================================================== ///

    fn process_type_declarations(&self) {
        for comp_unit in &self.dwarf_objects {
            // debug!("[process_type_declarations] comp_unit: {:#?}", comp_unit);
            self.create_type_declarations(&comp_unit);
        }
    }

    fn create_type_declarations(&self, comp_unit: &DwarfObject) {
        for (_offset, dwarf_object) in &comp_unit.child_tags {
            match &dwarf_object.tag_name[..] {
                "DW_TAG_structure_type" | "DW_TAG_base_type" => {
                    if let Some(dwarf_attr) = dwarf_object.attrs.get("DW_AT_name") {
                        if let DwarfAttributeValue::StringAttr(name) = dwarf_attr {
                            let name = name.clone();
                            let size_in_bytes = match dwarf_object.attrs.get("DW_AT_byte_size") {
                                Some(dwarf_attr) => {
                                    if let DwarfAttributeValue::NumericAttr(value) = dwarf_attr {
                                        *value
                                    } else {
                                        0
                                    }
                                }
                                _ => 0,
                            };
                            let mut field_decls = vec![];
                            for (_child_offset, member_object) in &dwarf_object.child_tags {
                                if member_object.tag_name == "DW_TAG_member" {
                                    let field_name = match member_object.attrs.get("DW_AT_name") {
                                        Some(dwarf_attr) => {
                                            if let DwarfAttributeValue::StringAttr(field_name) =
                                                dwarf_attr
                                            {
                                                field_name.clone()
                                            } else {
                                                panic!("[create_type_declarations] Name of field should be a string attribute.");
                                            }
                                        }
                                        _ => {
                                            warn!("[create_type_declarations] Struct {} has a no-name field.", name);
                                            "".to_string()
                                        }
                                    };
                                    let field_member_location = match member_object
                                        .attrs
                                        .get("DW_AT_data_member_location")
                                    {
                                        Some(dwarf_attr) => {
                                            if let DwarfAttributeValue::NumericAttr(value) =
                                                dwarf_attr
                                            {
                                                *value
                                            } else {
                                                panic!("[create_type_declarations] Location of member should be numeric in struct {}.", name);
                                            }
                                        }
                                        _ => 0,
                                    };
                                    let field_size_in_bytes = match member_object
                                        .attrs
                                        .get("DW_AT_type")
                                    {
                                        Some(dwarf_attr) => {
                                            if let DwarfAttributeValue::NumericAttr(value) =
                                                dwarf_attr
                                            {
                                                self.get_type_byte_size(
                                                    &(*value as usize),
                                                    comp_unit,
                                                )
                                                .unwrap_or(0)
                                            } else {
                                                panic!("[create_type_declarations] Size of member should be numeric in struct {}.", name);
                                            }
                                        }
                                        _ => 0,
                                    };
                                    field_decls.push(StructFieldDefinition {
                                        field_name,
                                        field_member_location,
                                        field_size_in_bytes,
                                    });
                                }
                            }
                            self.type_declarations.borrow_mut().insert(
                                name.clone(),
                                Rc::new(TypeDefinition {
                                    name,
                                    size_in_bytes,
                                    field_decls,
                                }),
                            );
                        }
                    }
                }
                _ => (),
            }
        }
    }

    pub fn get_type_declaration(&self, id: &String) -> Rc<TypeDefinition> {
        Rc::clone(self.type_declarations.borrow().get(id).unwrap())
    }

    /// ========================================================================== ///
    /// Global variable helpers                                                    ///
    /// ========================================================================== ///

    fn process_global_variables(&self) {
        for comp_unit in &self.dwarf_objects {
            self.create_global_vars_map(&comp_unit);
        }
    }

    // FIXME: Take these helpers out of the impl
    fn get_str_attr(&self, dobj: &DwarfObject, id: &str) -> Result<String, NoSuchDwarfFieldError> {
        if let Some(attr) = dobj.attrs.get(id) {
            if let DwarfAttributeValue::StringAttr(name) = attr {
                Ok(name.clone())
            } else {
                Err(NoSuchDwarfFieldError {})
            }
        } else {
            Err(NoSuchDwarfFieldError {})
        }
    }

    // FIXME: Take these helpers out of the impl
    fn get_num_attr(&self, dobj: &DwarfObject, id: &str) -> Result<u64, NoSuchDwarfFieldError> {
        if let Some(attr) = dobj.attrs.get(id) {
            if let DwarfAttributeValue::NumericAttr(n) = attr {
                Ok(*n)
            } else {
                Err(NoSuchDwarfFieldError {})
            }
        } else {
            Err(NoSuchDwarfFieldError {})
        }
    }

    fn get_type_name(&self, index: &usize, comp_unit: &DwarfObject) -> String {
        if let Some(dobj) = comp_unit.child_tags.get(index) {
            if let Ok(name) = self.get_str_attr(dobj, "DW_AT_name") {
                name
            } else {
                if let Ok(id) = self.get_num_attr(dobj, "DW_AT_type") {
                    self.get_type_name(&(id as usize), comp_unit)
                } else {
                    panic!("[get_type_name] Not a valid type.")
                }
            }
        } else {
            panic!("[get_type_name] Could not find child with index {}.", index);
        }
    }

    fn create_global_vars_map(&self, comp_unit: &DwarfObject) {
        for (_child_offset, dwarf_object) in &comp_unit.child_tags {
            if &dwarf_object.tag_name == "DW_TAG_variable" {
                if let Some(dwarf_attribute) = dwarf_object.attrs.get("DW_AT_name") {
                    if let DwarfAttributeValue::StringAttr(name) = dwarf_attribute {
                        let name = name.clone();
                        // FIXME: Remove size_in_bytes
                        let (type_defn, size_in_bytes) = match dwarf_object.attrs.get("DW_AT_type")
                        {
                            Some(dwarf_attr) => match dwarf_attr {
                                DwarfAttributeValue::NumericAttr(value) => {
                                    let type_name =
                                        self.get_type_name(&(*value as usize), comp_unit);
                                    let type_defn = self.get_type_declaration(&type_name);
                                    let size = match self
                                        .get_type_byte_size(&(*value as usize), comp_unit)
                                    {
                                        Ok(size) => size,
                                        Err(_) => {
                                            warn!("[get_global_vars] Global {} has no type.", name);
                                            0
                                        }
                                    };
                                    (type_defn, size)
                                }
                                _ => panic!("[get_global_vars] Type should be numeric."),
                            },
                            _ => panic!(
                                "[get_global_vars] Could not find DW_AT_type attribute for {}",
                                name
                            ),
                        };
                        let memory_addr = match dwarf_object.attrs.get("DW_AT_location") {
                            Some(dwarf_attr) => {
                                if let DwarfAttributeValue::NumericAttr(address) = dwarf_attr {
                                    *address
                                } else {
                                    0
                                }
                            }
                            _ => 0,
                        };
                        let is_addr = (size_in_bytes == 0);
                        if memory_addr > 0 {
                            self.global_vars.borrow_mut().push(Rc::new(GlobalVariable {
                                name,
                                size_in_bytes,
                                type_defn,
                                memory_addr,
                                is_addr,
                            }));
                        } else {
                            // warn!("[get_global_vars] Could not find memory address of global variable {}.", name);
                        }
                    }
                }
            }
        }
    }

    pub fn get_global_var_type(&self, name: &str) -> Rc<TypeDefinition> {
        Rc::clone(
            &self
                .global_vars
                .borrow()
                .iter()
                .find(|e| e.name == name)
                .unwrap()
                .type_defn,
        )
    }

    pub fn is_global_var(&self, name: &str) -> bool {
        self.global_vars
            .borrow()
            .iter()
            .find(|e| e.name == name)
            .is_some()
    }

    pub fn get_global_vars(&self) -> Vec<Rc<GlobalVariable>> {
        self.global_vars.borrow().clone()
    }

    /// ========================================================================== ///
    /// Helper functions                                                           ///
    /// ========================================================================== ///

    fn get_type_byte_size(
        &self,
        dwarf_object_index: &usize,
        comp_unit: &DwarfObject,
    ) -> Result<u64, NoSuchDwarfFieldError> {
        if let Some(dwarf_object) = comp_unit.child_tags.get(dwarf_object_index) {
            match &dwarf_object.tag_name[..] {
                "DW_TAG_typedef" | "DW_TAG_volatile_type" => {
                    let next_type_index = match dwarf_object.attrs
                            .get("DW_AT_type")
                            .unwrap_or_else(|| panic!("[get_type_byte_size] Type definition at address {} didn't have a DW_AT_type tag.", dwarf_object.offset))
                            {
                                DwarfAttributeValue::NumericAttr(value) => value.clone(),
                                _=> panic!("[get_type_byte_size] Should be numeric index."),
                            };
                    self.get_type_byte_size(&(next_type_index as usize), comp_unit)
                }
                "DW_TAG_base_type" | "DW_TAG_enumeration_type" | "DW_TAG_pointer_type" => {
                    match dwarf_object.attrs.get("DW_AT_byte_size")
                    .unwrap_or_else(|| panic!("[get_type_byte_size] No DW_AT_byte_size tag inside base type at address {}.", dwarf_object.offset)) {
                        DwarfAttributeValue::NumericAttr(value) => Ok(value.clone()),
                        _ => panic!("[get_type_byte_size] DW_AT_byte_size should be a numeric value."),
                    }
                },
                "DW_TAG_structure_type" | "DW_TAG_array_type" => {
                    // FIXME: This will only work for GCC!!
                    // NOTE: I believe riscv gcc compiler will use base pointers for 
                    //       the structs on the stack and memory as well as arrays.
                    //       So using pointer length in this case is enough information
                    // Ok(self.xlen / 8)
                    Ok(0)
                },
                _ => {
                    debug!("[get_type_byte_size] Not a type dwarf object!");
                    Err(NoSuchDwarfFieldError {})
                },
            }
        } else {
            debug!(
                "[get_type_byte_size] No such node at address {}.",
                dwarf_object_index
            );
            Err(NoSuchDwarfFieldError {})
        }
    }

    /// ========================================================================== ///
    /// Functions for processing dwarf files                                       ///
    /// ========================================================================== ///

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
            let mut file_objects = DwarfReader::process_dwarf_file_object(&object, endian)?;
            // debug!("file_objects: {:#?}", file_objects);
            dwarf_objects.append(&mut file_objects);
        }
        // debug!("{:#?}", dwarf_objects);
        Ok(dwarf_objects)
    }

    fn process_dwarf_file_object(
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
                DwarfReader::entries_to_dwarf_object(&unit, &dwarf, &mut entries_cursor)?
            {
                // info!("Compilation unit: \n{:#?}", &dwarf_object);
                dwarf_objects.push(dwarf_object);
            }
        }
        Ok(dwarf_objects)
    }

    fn entries_to_dwarf_object<R: gimli::Reader<Offset = usize>>(
        unit: &gimli::Unit<R>,
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
                DwarfReader::gimli_attr_to_dwarf_attr_map(unit, entry, dwarf)?,
                BTreeMap::new(),
            );
            parent = DwarfObject::create(format!("dummy"), 0, BTreeMap::new(), BTreeMap::new());
            parent.add_child_tag(first_dwarf_object);
            // DFS traverse through the remaining nodes
            while let Some((delta_depth, entry)) = entries_cursor.next_dfs()? {
                match delta_depth {
                    // If increasing depth, then extract the parent from the current parent's last child
                    _ if delta_depth > 0 => {
                        assert!(delta_depth == 1, "[entries_to_dwarf_object] Depth of DWARF node increased by more than 1! Probably an ill-formed DWARF format.");
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
                // debug!("[entries_to_dwarf_object] Adding child {} to parent.", entry.offset().0);
                parent.add_child_tag(DwarfObject::create(
                    entry.tag().to_string(),
                    entry.offset().0,
                    DwarfReader::gimli_attr_to_dwarf_attr_map(unit, entry, dwarf)?,
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
        unit: &gimli::Unit<R>,
        entry: &gimli::DebuggingInformationEntry<R>,
        dwarf: &gimli::Dwarf<R>,
    ) -> Result<BTreeMap<String, DwarfAttributeValue>, gimli::Error> {
        let mut attributes = BTreeMap::new();
        let mut attrs_cursor = entry.attrs();
        while let Some(attr) = attrs_cursor.next()? {
            if let Some(attr_value) = DwarfReader::get_attr_value(unit, &attr, dwarf)? {
                attributes.insert(attr.name().to_string(), attr_value);
            }
        }
        Ok(attributes)
    }

    fn get_attr_value<R: gimli::Reader<Offset = usize>>(
        unit: &gimli::Unit<R>,
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
            gimli::AttributeValue::Exprloc(data) => {
                let mut pc = data.0.clone();
                match gimli::Operation::parse(&mut pc, &data.0, unit.encoding()) {
                    Ok(op) => match op {
                        gimli::Operation::Address { address } => {
                            Some(DwarfAttributeValue::NumericAttr(address))
                        }
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        };
        Ok(attr_value)
    }
}
