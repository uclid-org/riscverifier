use object::Object;
use std::{borrow, fs};
use std::convert::TryInto;

#[derive(Debug)]
pub struct DwarfReader {
    compile_units: Vec<DwarfObject>
    // function_sigs: Vec<FunctionSig>,
    // global_vars: Vec<GlobalVar>
}

#[derive(Debug)]
pub struct FunctionSig {
    name: String,
    formal_args: Vec<(String, u64)>,
    return_size: u64,
    addr: u64
}

#[derive(Debug)]
pub struct GlobalVariable {
    name: String,
    addr: u64,
    size: u64
}

#[derive(Debug)]
pub struct DwarfObject {
    tag_name: String,
    offset: usize,
    attrs: Vec<DwarfAttribute>,
    child_tags: Vec<DwarfObject>
}

#[derive(Debug)]
pub enum DwarfAttribute {
    NumericAttr(String, u64),
    StringAttr(String, String)
}

#[derive(Debug, Clone)]
struct RuntimeError; // FIXME: put errors in a spearate folder

impl DwarfObject {
    pub fn create(tag_name: String, offset: usize, attrs: Vec<DwarfAttribute>, child_tags: Vec<DwarfObject>) -> DwarfObject {
        DwarfObject {
            tag_name,
            offset,
            attrs,
            child_tags
        }
    }

    pub fn add_child_tag(&mut self, dwarf_object: DwarfObject) {
        self.child_tags.push(dwarf_object);
    }

    pub fn last_child(&mut self) -> DwarfObject {
        self.child_tags.pop().unwrap()
    }
}

impl DwarfReader {
    
    pub fn create(files: Vec<String>) -> DwarfReader {
        DwarfReader { compile_units: DwarfReader::process_dwarf_files(files).expect("Unable to parse binary files.") }
    }

    //

    pub fn get_global_addr(&self, global_name: &str) -> u64 {
        0
    }

    fn process_dwarf_files(files: Vec<String>) -> Result<Vec<DwarfObject>, gimli::Error> {
        let mut dwarf_objects = vec![];
        for path in files {
            let file = fs::File::open(&path[..]).unwrap();
            let mmap = unsafe { memmap::Mmap::map(&file).unwrap() };
            let object = object::File::parse(&*mmap).unwrap();
            let endian = if object.is_little_endian() {
                gimli::RunTimeEndian::Little
            } else {
                gimli::RunTimeEndian::Big
            };
            let mut file_objects = DwarfReader::process_dwarf_file(&object, endian)?;
            dwarf_objects.append(&mut file_objects);
        }
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
            // // FIXME: Remove this later
            if format!("{:x}", header.offset().0) != "18383" {
                continue;
            }
            debug!("[process_dwarf_file] Processing unit at <.debug_info+0x{:x}>", header.offset().0);
            let unit = dwarf.unit(header)?;
            // Iterate over the Debugging Information Entries (DIEs) in the unit.
            let mut entries_cursor = unit.entries();
            if let Some(dwarf_object) = DwarfReader::entries_to_dwarf_object(&dwarf, &mut entries_cursor)? {
                info!("Compilation unit: \n{:#?}", &dwarf_object);
                // let mut entries_cursor = unit.entries();
                // self.print_gimli_dwarf(&dwarf, &mut entries_cursor);
                dwarf_objects.push(dwarf_object);
            }
        }
        Ok(dwarf_objects)
    }

    fn get_attr_value<R: gimli::Reader<Offset = usize>>(
        attr: &gimli::Attribute<R>,
        dwarf: &gimli::Dwarf<R>
    ) -> Result<Option<DwarfAttribute>, gimli::Error> {
        let name = attr.name().to_string();
        let value = attr.value();
        let attr_value = match value {
            gimli::AttributeValue::DebugStrRef(offset) => {
                let s = dwarf.debug_str.get_str(offset)?;
                Some(DwarfAttribute::StringAttr(name, format!("{}", s.to_string_lossy()?)))
            }
            gimli::AttributeValue::Udata(data) => {
                Some(DwarfAttribute::NumericAttr(name, data))
            }
            gimli::AttributeValue::UnitRef(offset) => {
                Some(DwarfAttribute::NumericAttr(name, offset.0 as u64))
            }
            _ => {
                warn!("[get_attr_value] Could not extract attribute value: {:?}.", attr.value());
                None
            }
        };
        Ok(attr_value)
    }

    fn print_gimli_dwarf<R: gimli::Reader<Offset = usize>>(
        dwarf: &gimli::Dwarf<R>,
        entries_cursor: &mut gimli::EntriesCursor<R>
    ) -> Result<(), gimli::Error> {
        let mut depth = 0;
        while let Some((delta_depth, entry)) = entries_cursor.next_dfs()? {
            let tag_name = entry.tag().to_string();
            depth += delta_depth;
            info!("[print_gimli_dwarf] Depth: {} -- Offset {:x} -- Processing {} ==============", depth, entry.offset().0, tag_name);
            // Iterate over the attributes in the DIE.
            let mut attrs_cursor = entry.attrs();
            while let Some(attr) = attrs_cursor.next()? {
                let attr_name = attr.name().to_string();
                let attr_value = DwarfReader::get_attr_value(&attr, dwarf)?;
                info!("[print_gimli_dwarf] {}{}: {:?}", "   ".repeat(depth.try_into().unwrap()), &attr_name, &attr_value);
            }
        }
        Ok(())
    }

    fn entries_to_dwarf_object<R: gimli::Reader<Offset = usize>>(
        dwarf: &gimli::Dwarf<R>,
        entries_cursor: &mut gimli::EntriesCursor<R>
    ) -> Result<Option<DwarfObject>, gimli::Error> {
        let mut dwarf_object_stack = vec![];
        let mut parent;
        if let Some((_, entry)) = entries_cursor.next_dfs()? {
            debug!("[gimli_unit_to_dwarf_object] Processing the first node... {}", entry.tag().to_string());
            // Create dummy node to store unit
            let first_dwarf_object = DwarfObject::create(entry.tag().to_string(), entry.offset().0, DwarfReader::gimli_attr_to_dwarf_attr(entry, dwarf)?, vec![]);
            parent = DwarfObject::create(format!("dummy"), 0, vec![], vec![first_dwarf_object]);
            // Iterate through the remaining nodes
            while let Some((delta_depth, entry)) = entries_cursor.next_dfs()? {
                debug!("[gimli_unit_to_dwarf_object] Processing next node... <{}> {}", delta_depth, entry.tag().to_string());
                match delta_depth {
                    _ if delta_depth > 0 => {
                        let mut grandparent = parent;
                        parent = grandparent.last_child();
                        dwarf_object_stack.push(grandparent);
                    }
                    _ if delta_depth < 0 => {
                        for _ in 0..-delta_depth {
                            let mut grandparent = dwarf_object_stack.pop().unwrap();
                            grandparent.add_child_tag(parent);
                            parent = grandparent;
                        }
                    }
                    _ => ()
                }
                parent.add_child_tag(DwarfObject::create(entry.tag().to_string(), entry.offset().0, DwarfReader::gimli_attr_to_dwarf_attr(entry, dwarf)?, vec![]));
            }
            while dwarf_object_stack.len() > 1 {
                let mut grandparent = dwarf_object_stack.pop().unwrap();
                grandparent.add_child_tag(parent);
                parent = grandparent;
            }
            return Ok(Some(parent))
        }
        Ok(None)
    }

    fn gimli_attr_to_dwarf_attr<R: gimli::Reader<Offset = usize>>(
        entry: &gimli::DebuggingInformationEntry<R>,
        dwarf: & gimli::Dwarf<R>
    ) -> Result<Vec<DwarfAttribute>, gimli::Error> {
        let mut attributes = vec![];
        let mut attrs_cursor = entry.attrs();
        while let Some(attr) = attrs_cursor.next()? {
            if let Some(attr_value) = DwarfReader::get_attr_value(&attr, dwarf)? {
                attributes.push(attr_value);
            }
        }
        Ok(attributes)
    }
}
