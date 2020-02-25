use object::Object;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::{borrow, fs, rc::Rc};

use crate::translator;
use crate::utils;

#[derive(Debug, Clone)]
pub struct DwarfVar {
    pub name: String,
    pub typ_defn: Rc<DwarfTypeDefn>,
    pub memory_addr: u64,
}
impl DwarfVar {
    pub fn new(name: String, typ_defn: Rc<DwarfTypeDefn>, memory_addr: u64) -> Self {
        DwarfVar {
            name,
            typ_defn,
            memory_addr,
        }
    }
}

#[derive(Debug)]
pub struct DwarfFuncSig {
    pub name: String,
    pub args: Vec<DwarfVar>,
    pub ret_typ_defn: Option<Rc<DwarfTypeDefn>>,
}
impl DwarfFuncSig {
    pub fn new(name: String, args: Vec<DwarfVar>, ret_typ_defn: Option<Rc<DwarfTypeDefn>>) -> Self {
        DwarfFuncSig {
            name,
            args,
            ret_typ_defn,
        }
    }
}

#[derive(Debug, Clone)]
pub enum DwarfTypeDefn {
    Primitive {
        bytes: u64,
    },
    Array {
        in_typ: Rc<DwarfTypeDefn>,
        out_typ: Rc<DwarfTypeDefn>,
    },
    Struct {
        id: String,
        fields: HashMap<String, StructField>,
        bytes: u64,
    },
    Pointer {
        value_typ: Rc<DwarfTypeDefn>,
    },
}
impl DwarfTypeDefn {
    pub fn to_bytes(&self) -> u64 {
        match self {
            DwarfTypeDefn::Primitive { bytes }
            | DwarfTypeDefn::Struct {
                id: _,
                fields: _,
                bytes,
            } => *bytes,
            DwarfTypeDefn::Array { .. } => 8, // FIXME: XLEN
            DwarfTypeDefn::Pointer { .. } => 8,
        }
    }
}
#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub typ: Rc<DwarfTypeDefn>,
    pub loc: u64,
}

#[derive(Debug)]
pub struct DwarfObject {
    pub tag_name: String,
    pub offset: u64,
    pub attrs: BTreeMap<String, DwarfAttributeValue>,
    pub child_tags: BTreeMap<u64, DwarfObject>,
}
impl DwarfObject {
    pub fn create(
        tag_name: String,
        offset: u64,
        attrs: BTreeMap<String, DwarfAttributeValue>,
        child_tags: BTreeMap<u64, DwarfObject>,
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
    pub fn get_child(&self, index: &u64) -> Result<&DwarfObject, utils::Error> {
        self.child_tags
            .get(index)
            .map_or_else(|| Err(utils::Error::CouldNotFindDwarfChild), |v| Ok(v))
    }
    pub fn get_child_named(&self, tag_name: &str) -> Result<&DwarfObject, utils::Error> {
        self.child_tags
            .iter()
            .find(|(_os, dobj)| dobj.tag_name == tag_name)
            .map_or_else(|| Err(utils::Error::CouldNotFindDwarfChild), |v| Ok(v.1))
    }
    pub fn get_attr(&self, attr: &str) -> Result<&DwarfAttributeValue, utils::Error> {
        self.attrs
            .get(attr)
            .map_or_else(|| Err(utils::Error::NoSuchDwarfFieldError), |v| Ok(v))
    }
}

#[derive(Debug)]
pub enum DwarfAttributeValue {
    NumericAttr(u64),
    StringAttr(String),
    BooleanAttr(bool),
}
impl DwarfAttributeValue {
    pub fn get_expect_num_val(&self) -> &u64 {
        match self {
            DwarfAttributeValue::NumericAttr(v) => v,
            _ => panic!("[get_expect_num_val] Not a numeric attribute."),
        }
    }
    pub fn get_expect_str_val(&self) -> &String {
        match self {
            DwarfAttributeValue::StringAttr(v) => v,
            _ => panic!("[get_expect_num_val] Not a numeric attribute."),
        }
    }
    #[allow(dead_code)]
    pub fn get_expect_bool_val(&self) -> &bool {
        match self {
            DwarfAttributeValue::BooleanAttr(v) => v,
            _ => panic!("[get_expect_num_val] Not a numeric attribute."),
        }
    }
}

pub trait DwarfInterface: std::fmt::Debug {
    /// ===================== DWARF Reader functions =================
    /// Process the function signatures from the DwarfObject
    fn process_func_sigs(dobj: &DwarfObject) -> Vec<DwarfFuncSig>;
    /// Process the list of global variables for the DwarfObject
    fn process_global_vars(dobj: &DwarfObject) -> Vec<DwarfVar>;
    /// Creates the type searching in comp_unit with the DwarfObject index
    fn get_type(index: &u64, comp_unit: &DwarfObject) -> Result<Rc<DwarfTypeDefn>, utils::Error>;
    /// ====================== Helper functions ======================
    /// Parses the binary files in the paths and returns
    /// the corresponding DwarfObjects from the debugging information
    fn process_dwarf_files(paths: &Vec<String>) -> Result<Vec<DwarfObject>, gimli::Error> {
        let mut dwarf_objects = vec![];
        for path in paths {
            let mut dwarf_object = Self::process_dwarf_file(path)?;
            dwarf_objects.append(&mut dwarf_object);
        }
        // debug!("[process_dwarf_files] dwarf_objects: {:#?}", dwarf_objects);
        Ok(dwarf_objects)
    }

    /// Parses the specified binary file in the path and returns
    /// the corresponding DwarfObjects from the debugging information
    fn process_dwarf_file(path: &String) -> Result<Vec<DwarfObject>, gimli::Error> {
        info!("[process_dwarf_file] Processing dwarf file {:?}.", path);
        let file = fs::File::open(&path[..]).unwrap();
        let mmap = unsafe { memmap::Mmap::map(&file).unwrap() };
        let object = object::File::parse(&*mmap).unwrap();
        let endian = if object.is_little_endian() {
            gimli::RunTimeEndian::Little
        } else {
            gimli::RunTimeEndian::Big
        };
        Ok(Self::process_dwarf_file_object(&object, endian)?)
    }

    /// Converts an object file into a vector of DwarfObjects
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
            let unit = dwarf.unit(header)?;
            // Iterate over the Debugging Information Entries (DIEs) in the unit.
            let mut entries_cursor = unit.entries();
            if let Some(dwarf_object) =
                Self::entries_to_dwarf_object(&unit, &dwarf, &mut entries_cursor)?
            {
                // info!("Compilation unit: \n{:#?}", &dwarf_object);
                dwarf_objects.push(dwarf_object);
            }
        }
        Ok(dwarf_objects)
    }

    /// Converts gimli entries_cursor to a DwarfObject
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
            // Create dummy node to store unit
            let first_dwarf_object = DwarfObject::create(
                entry.tag().to_string(),
                entry.offset().0 as u64,
                Self::gimli_attr_to_dwarf_attr_map(unit, entry, dwarf)?,
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
                    entry.offset().0 as u64,
                    Self::gimli_attr_to_dwarf_attr_map(unit, entry, dwarf)?,
                    BTreeMap::new(),
                ));
            }
            // Recursively add parent to grandparent until one node remains (dummy node in the stack and parent is the actual node to return)
            while dwarf_object_stack.len() > 1 {
                let mut grandparent = dwarf_object_stack.pop().unwrap();
                grandparent.add_child_tag(parent);
                parent = grandparent;
            }
            return Ok(Some(parent));
        }
        Ok(None)
    }

    /// Converts gimli attributes entry to attribute map
    fn gimli_attr_to_dwarf_attr_map<R: gimli::Reader<Offset = usize>>(
        unit: &gimli::Unit<R>,
        entry: &gimli::DebuggingInformationEntry<R>,
        dwarf: &gimli::Dwarf<R>,
    ) -> Result<BTreeMap<String, DwarfAttributeValue>, gimli::Error> {
        let mut attributes = BTreeMap::new();
        let mut attrs_cursor = entry.attrs();
        while let Some(attr) = attrs_cursor.next()? {
            if let Some(attr_value) = Self::get_attr_value(unit, &attr, dwarf)? {
                attributes.insert(attr.name().to_string(), attr_value);
            }
        }
        Ok(attributes)
    }

    /// Converts attribute value to a DwarfAttributeValue
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

pub struct DwarfReader<I>
where
    I: DwarfInterface,
{
    func_sigs: HashMap<String, DwarfFuncSig>,
    global_vars: Vec<DwarfVar>,
    _phantom_data: PhantomData<I>,
}

impl<I> DwarfReader<I>
where
    I: DwarfInterface,
{
    pub fn new(binary_paths: &Vec<String>) -> Result<DwarfReader<I>, gimli::Error> {
        let dwarf_obj_vec = I::process_dwarf_files(binary_paths)?;
        let func_sigs = dwarf_obj_vec
            .iter()
            .map(|comp_unit| I::process_func_sigs(comp_unit))
            .flatten()
            .map(|fs| (fs.name.clone(), fs))
            .collect::<HashMap<String, DwarfFuncSig>>();
        let global_vars = dwarf_obj_vec
            .iter()
            .map(|comp_unit| I::process_global_vars(comp_unit))
            .flatten()
            .collect();
        // info!("[new] Global Variables: {:#?}", global_vars);
        // info!("[new] Func Sigs: {:#?}", func_sigs);
        Ok(DwarfReader {
            func_sigs,
            global_vars,
            _phantom_data: PhantomData,
        })
    }
    #[allow(dead_code)]
    pub fn is_global_var(&self, name: &str) -> bool {
        self.global_vars.iter().find(|v| v.name == name).is_some()
    }
    pub fn global_vars(&self) -> &Vec<DwarfVar> {
        &self.global_vars
    }
    pub fn func_sig(&self, func_name: &str) -> Option<&DwarfFuncSig> {
        self.func_sigs.get(func_name)
    }
    pub fn func_sigs(&self) -> &HashMap<String, DwarfFuncSig> {
        &self.func_sigs
    }
    pub fn typ_map(&self) -> HashMap<String, Rc<DwarfTypeDefn>> {
        let mut typ_map = HashMap::new();
        for v in &self.global_vars {
            typ_map.insert(v.name.clone(), Rc::clone(&v.typ_defn));
        }
        for (fun_name, fs) in &self.func_sigs {
            for arg in &fs.args {
                typ_map.insert(
                    format!("{}${}", fun_name, arg.name),
                    Rc::clone(&arg.typ_defn),
                );
            }
            if let Some(ret_typ) = &fs.ret_typ_defn {
                typ_map.insert(format!("{}$$ret", fun_name), Rc::clone(ret_typ));
            }
        }
        // Add system variable types
        typ_map.insert(
            format!("${}", translator::EXCEPT_VAR),
            Rc::new(DwarfTypeDefn::Primitive { bytes: 64 }),
        ); // FIXME: Replace with xlen
        typ_map
    }
}
