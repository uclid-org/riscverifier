#[macro_use]
extern crate log;
extern crate env_logger;

extern crate clap;
use clap::{App, Arg};

extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate asts;
extern crate dwarf_ctx;
extern crate rv_model;

extern crate topological_sort;

pub mod disassembler;
use disassembler::disassembler::Disassembler;

pub mod translator;
use translator::Translator;

pub mod verification_interfaces;
use verification_interfaces::uclidinterface::Uclid5Interface;

pub mod datastructures;
use datastructures::cfg::BasicBlock;

pub mod spec_template_generator;
use spec_template_generator::SpecTemplateGenerator;

pub mod ir_interface;

pub mod utils;

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fs::File,
    io::prelude::*,
    rc::Rc,
};

use dwarf_ctx::{
    dwarf_interfaces::cdwarfinterface::CDwarfInterface,
    dwarfreader::{DwarfCtx, DwarfReader, DwarfTypeDefn},
};

use asts::spec_lang::{sl_ast, sl_ast::ASTRewriter, sl_parser};

use rv_model::system_model;

// ================================================================================================
/// # RICS-V Translator Main Function

/// Process the commands given to the tool
pub fn process_commands() {
    let matches = cl_options().get_matches();
    let xlen = utils::dec_str_to_u64(matches.value_of("xlen").unwrap_or("64"))
        .expect("[main] Unable to parse numberic xlen.");
    if xlen != 64 {
        warn!("uclidinterface is hard-coded with 64 bit dependent definitions.");
        panic!("[main] Non-64 bit XLEN is not yet implemented.");
    }
    // Parse function blocks from binary
    let binary_paths = matches
        .value_of("binaries")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Disassemble binaries and create basic blocks
    let mut disassembler = Disassembler::new(None, Some("debug_log"));
    let als = disassembler.read_binaries(&binary_paths);
    let bbs = BasicBlock::split(&als);
    // Module name
    let module_name = matches.value_of("modname").unwrap_or("main");
    // Initialize DWARF reader
    let dwarf_reader: Rc<DwarfReader<CDwarfInterface>> =
        Rc::new(DwarfReader::new(&xlen, &binary_paths).unwrap());
    // Function to generate
    let func_names = matches
        .value_of("function")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Specification
    let spec_files = matches
        .value_of("spec")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    let specs_map = process_specs(&spec_files, &dwarf_reader.ctx());
    // Get ignored functions
    let ignored_funcs = matches
        .value_of("ignore-funcs")
        .map_or(HashSet::new(), |lst| {
            lst.split(",").collect::<HashSet<&str>>()
        });
    // Get list of functions to verify
    let verify_funcs = matches
        .value_of("verify-funcs")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Flag for ignoring and inlining functions
    let ignore_specs = matches.is_present("ignore-specs");
    // Translate and write to output file
    let mut translator: Translator<Uclid5Interface> = Translator::new(
        xlen,
        &module_name,
        &bbs,
        &ignored_funcs,
        &verify_funcs,
        dwarf_reader.ctx(),
        &specs_map,
        ignore_specs,
    );
    for func_name in func_names {
        translator.gen_func_model(&func_name);
    }
    // Print model to file
    let model_str = translator.print_model();
    if let Some(output_file) = matches.value_of("output") {
        let res = File::create(output_file)
            .ok()
            .unwrap()
            .write_all(model_str.as_bytes());
        match res {
            Ok(_) => info!("Successfully wrote model to {}", output_file),
            Err(_) => panic!("Unable to write model to {}", output_file),
        }
    }
    // Print all specification template
    if let Some(output_file) = matches.value_of("spec_template") {
        let funcs: HashSet<String> = dwarf_reader.ctx().func_sigs().keys().cloned().collect();
        let spec_template_str = SpecTemplateGenerator::fun_templates(&funcs, dwarf_reader.ctx());
        let res = File::create(output_file)
            .ok()
            .unwrap()
            .write_all(spec_template_str.as_bytes());
        match res {
            Ok(_) => info!(
                "Successfully wrote specification template to {}",
                output_file
            ),
            Err(_) => panic!("Unable to write specificaiton template to {}", output_file),
        }
    }
    translator.clear();
}

// ===========================================================================================
/// # Command Line Interface

fn cl_options<'t, 's>() -> App<'t, 's> {
    App::new("RISCVerifier")
        .version("1.0")
        .author("Kevin Cheang <kcheang@berkeley.edu>")
        .about("Translates RISC-V assembly (support for 64g only) programs into an IR")
        .arg(
            Arg::with_name("binaries")
                .short("b")
                .long("binary")
                .help("RISC-V binary file.")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("modname")
                .short("n")
                .long("modname")
                .help("UCLID module name")
                .required(false)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("spec")
                .short("s")
                .long("spec")
                .help("RISC-V specification file.")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("output")
                .help("Specify the output path.")
                .short("o")
                .long("output")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("spec_template")
                .help("Specify the specification template output file.")
                .short("t")
                .long("spec_template")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("function")
                .help("Specify a list of functions to verify.")
                .short("f")
                .long("function")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("xlen")
                .help("Specify the architecture XLEN.")
                .short("x")
                .long("xlen")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("ignore-funcs")
                .help("Comma separated list of functions to ignore. E.g. \"foo,bar\"")
                .short("i")
                .long("ignore-funcs")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("verify-funcs")
                .help("List of functions to verify.")
                .short("v")
                .long("verify-funcs")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("ignore-specs")
                .help("List of functions to verify.")
                .long("ignore-specs")
                .takes_value(false),
        )
}

// ====================================================================================================
/// # Specifications

pub fn process_specs(
    spec_files: &Vec<&str>,
    dwarf_ctx: &DwarfCtx,
) -> HashMap<String, Vec<sl_ast::Spec>> {
    // Parse specifications
    let spec_parser = sl_parser::SpecParser::new();
    let fun_specs_vec = spec_parser
        .process_spec_files(spec_files)
        .expect("Could not read spec.");

    // Run a set of passes over each individual specification expression
    let mut ret = HashMap::new();
    for mut fun_spec in fun_specs_vec {
        let fname = fun_spec.fname.to_string();
        let specs = &mut fun_spec.specs;
        for spec in specs {
            match spec {
                sl_ast::Spec::Requires(bexpr) | sl_ast::Spec::Ensures(bexpr) => {
                    sl_bexpr_rewrite_passes(bexpr, dwarf_ctx, &fname[..]);
                }
                _ => (),
            }
        }
        ret.insert(fname, fun_spec.specs);
    }
    ret
}

fn sl_bexpr_rewrite_passes(bexpr: &mut sl_ast::BExpr, dwarf_ctx: &DwarfCtx, fname: &str) {
    // Type inference pass. Before the initial pass, we expect the specficiation
    // AST to have Unknown types for all VExpr.
    VExprTypeInference::rewrite_bexpr(
        bexpr,
        &RefCell::new((dwarf_ctx, fname, &mut HashMap::new())),
    );
    // Rewrite all quantified variable names. Identifiers that are global variables are
    // replaced with a function application and prefix that calls an alias.
    RenameGlobals::rewrite_bexpr(bexpr, &RefCell::new(dwarf_ctx));
}

// ====================================================================================================
/// ## Specification transformation passes

/// AST pass that renames the identifiers for global variables from
/// Identifiers `name` to FuncApp `global_var_name()`.
struct RenameGlobals {}
impl sl_ast::ASTRewriter<&DwarfCtx> for RenameGlobals {
    fn rewrite_vexpr_ident(ident: &mut sl_ast::VExpr, context: &RefCell<&DwarfCtx>) {
        if is_global(ident, &*context.borrow()) {
            match ident {
                sl_ast::VExpr::Ident(name, typ) => {
                    *ident =
                        sl_ast::VExpr::FuncApp(format!("global_var_{}", name), vec![], typ.clone());
                }
                _ => panic!("Expected identifier."),
            }
        }
    }
}

/// AST pass that automatically infers and rewrites the type of the VExpr
struct VExprTypeInference {}
impl sl_ast::ASTRewriter<(&DwarfCtx, &str, &mut HashMap<String, sl_ast::VType>)>
    for VExprTypeInference
{
    /// Add the bound variable to the type map when it's encountered in a quantifier
    fn rewrite_bexpr_boolop(
        vop: &mut sl_ast::BoolOp,
        context: &RefCell<(&DwarfCtx, &str, &mut HashMap<String, sl_ast::VType>)>,
    ) {
        let mut borrowed_ctx = context.borrow_mut();
        // Add the types of the bound variables to the type map
        match vop {
            sl_ast::BoolOp::Forall(v, _) => borrowed_ctx
                .2
                .insert(v.get_ident_name().to_string(), v.typ().clone()),
            sl_ast::BoolOp::Exists(v, _) => borrowed_ctx
                .2
                .insert(v.get_ident_name().to_string(), v.typ().clone()),
            _ => None,
        };
    }

    /// Replace the identifiers with their actual types (instead of unknown)
    fn rewrite_vexpr_ident(
        vexpr: &mut sl_ast::VExpr,
        context: &RefCell<(&DwarfCtx, &str, &mut HashMap<String, sl_ast::VType>)>,
    ) {
        let borrowed_ctx = context.borrow();
        // Unpack the context tuple
        let dwarf_ctx = borrowed_ctx.0;
        let fname = borrowed_ctx.1;
        let typ_map = &borrowed_ctx.2;

        // Initialize a type option to store the identifier type
        let mut typ_opt;
        // Identifier name
        let var_id = vexpr.get_ident_name();

        // Check if it's a system variable
        let xlen = dwarf_ctx.xlen;
        typ_opt = match &var_id[..] {
            system_model::PC_VAR => {
                Some(sl_ast::VType::from_ast_type(&system_model::pc_type(xlen)))
            }
            system_model::RETURNED_FLAG => {
                Some(sl_ast::VType::from_ast_type(&system_model::returned_type()))
            }
            system_model::PRIV_VAR => {
                Some(sl_ast::VType::from_ast_type(&system_model::priv_type()))
            }
            system_model::MEM_VAR => {
                Some(sl_ast::VType::from_ast_type(&system_model::mem_type(xlen)))
            }
            system_model::A0 | system_model::SP | system_model::RA => {
                Some(sl_ast::VType::from_ast_type(&system_model::bv_type(xlen)))
            }
            _ => None,
        };

        // Check if it's a formal argument
        let func_sig_opt = dwarf_ctx.func_sigs().get(&fname[..]);
        if let Some(func_sig) = func_sig_opt {
            let formal_arg_opt = func_sig.args.iter().find(|dv| dv.name == var_id);
            if let Some(fa) = formal_arg_opt {
                typ_opt = Some(from_dwarf_type(&fa.typ_defn));
            }
        }

        // Bound variable; find in type map `typ_map`
        typ_opt = typ_opt.or_else(|| {
            typ_map
                .get(&var_id[..])
                .map_or(None, |typ| Some(typ.clone()))
        });

        // Global variable
        // NOTE: formals takes shadow precedence over globals
        let mut is_global = false;
        if typ_opt.is_none() {
            let dt_res = dwarf_ctx.global_var_type(&var_id);
            if dt_res.is_err() {
                // Unable to find any type. Must be struct field.
                return;
            }
            typ_opt = Some(from_dwarf_type(&dt_res.unwrap()));
            is_global = true;
        }

        assert!(
            typ_opt.is_some(),
            "Unable to find variable {} in DWARF info.",
            &var_id
        );
        let global_addr = sl_ast::VExpr::Ident(format!("{}", var_id), typ_opt.clone().unwrap());
        *vexpr = if is_global {
            match &typ_opt.clone().unwrap() {
                sl_ast::VType::Bv(_) => {
                    // Primitive type; dereference this global
                    sl_ast::VExpr::OpApp(
                        sl_ast::ValueOp::Deref,
                        vec![global_addr],
                        typ_opt.clone().unwrap(),
                    )
                }
                _ => global_addr,
            }
        } else {
            // FIXME: formals are all xlen for now
            sl_ast::VExpr::Ident(var_id.to_string(), sl_ast::VType::Bv(dwarf_ctx.xlen as u16))
        };
    }

    /// Infer types for the operator applications of VExprs
    fn rewrite_vexpr_opapp(
        opapp: &mut sl_ast::VExpr,
        context: &RefCell<(&DwarfCtx, &str, &mut HashMap<String, sl_ast::VType>)>,
    ) {
        match opapp {
            sl_ast::VExpr::OpApp(op, exprs, _) => {
                Self::rewrite_vexpr_valueop(op, context);
                Self::rewrite_vexprs(exprs, context);

                let new_exprs = exprs.clone();
                let new_typ = sl_ast::VType::infer_op_type(op, &new_exprs);

                *opapp = match &op {
                    sl_ast::ValueOp::GetField => {
                        // Implicit dereference for field operator if the type is a primitive
                        let struct_type = &new_exprs[0].typ();
                        let field_name = &new_exprs[1].get_ident_name();
                        let field_type = match struct_type {
                            sl_ast::VType::Struct {
                                id: _,
                                fields,
                                size: _,
                            } => *fields
                                .get(&field_name[..])
                                .expect(&format!("Unable to find struct field {}.", field_name))
                                .clone(),
                            _ => panic!("Expected struct type for variable {:?}.", new_exprs[0]),
                        };
                        // This opapp has the field type infered
                        let field_ident = sl_ast::VExpr::Ident(
                            new_exprs[1].get_ident_name().to_string(),
                            field_type.clone(),
                        );
                        let new_opapp = sl_ast::VExpr::OpApp(
                            op.clone(),
                            vec![new_exprs[0].clone(), field_ident],
                            new_typ,
                        );
                        match &field_type {
                            sl_ast::VType::Bv(_) => sl_ast::VExpr::OpApp(
                                sl_ast::ValueOp::Deref,
                                vec![new_opapp],
                                field_type,
                            ),
                            _ => new_opapp,
                        }
                    }
                    sl_ast::ValueOp::ArrayIndex => {
                        // Implicit dereference for array index if the type is a primitive
                        match &new_exprs[0].typ() {
                            sl_ast::VType::Array {
                                in_type: _,
                                out_type,
                            } => match &**out_type {
                                sl_ast::VType::Bv(_) => sl_ast::VExpr::OpApp(
                                    sl_ast::ValueOp::Deref,
                                    vec![opapp.clone()],
                                    *out_type.clone(),
                                ),
                                _ => sl_ast::VExpr::OpApp(op.clone(), new_exprs, new_typ),
                            },
                            _ => panic!("Expected array type for variable {:?}", new_exprs[0]),
                        }
                    }
                    // Update the expressions and infer the type for everything else
                    _ => sl_ast::VExpr::OpApp(op.clone(), new_exprs, new_typ),
                };
            }
            _ => panic!("Implementation error; expected `VExpr::OpApp`."),
        }
    }

    fn rewrite_vexpr_funcapp(
        funcapp: &mut sl_ast::VExpr,
        context: &RefCell<(&DwarfCtx, &str, &mut HashMap<String, sl_ast::VType>)>,
    ) {
        match funcapp {
            sl_ast::VExpr::FuncApp(fapp, exprs, typ) => {
                Self::rewrite_vexpr_funcid(fapp, context);
                Self::rewrite_vexprs(exprs, context);
                *typ = sl_ast::VType::infer_func_app_type(fapp, exprs);
            }
            _ => panic!("Implementation error; expected `VExpr::FuncApp`."),
        }
    }
}

// ================================================================================
/// # DWARF Helpers

/// Translates a DwarfTypeDefn to a specification variable type
fn from_dwarf_type(dtd: &DwarfTypeDefn) -> sl_ast::VType {
    match dtd {
        DwarfTypeDefn::Primitive { bytes }
        | DwarfTypeDefn::Pointer {
            value_typ: _,
            bytes,
        } => sl_ast::VType::Bv((bytes * system_model::BYTE_SIZE) as u16),
        DwarfTypeDefn::Array {
            in_typ,
            out_typ,
            bytes: _,
        } => sl_ast::VType::Array {
            in_type: Box::new(from_dwarf_type(in_typ)),
            out_type: Box::new(from_dwarf_type(out_typ)),
        },
        DwarfTypeDefn::Struct { id, fields, bytes } => {
            let id = id.to_string();
            let fields = fields
                .iter()
                .map(|kv| {
                    let field_name = (&*kv.0).clone();
                    let field_type = from_dwarf_type(&*kv.1.typ);
                    (field_name, Box::new(field_type))
                })
                .collect::<HashMap<String, Box<sl_ast::VType>>>();
            let size = bytes * system_model::BYTE_SIZE;
            sl_ast::VType::Struct { id, fields, size }
        }
    }
}

/// Helper function that determines if one of the VExprs from `vexprs`
/// is a global variable
pub fn is_global(vexpr: &sl_ast::VExpr, dwarf_ctx: &DwarfCtx) -> bool {
    match vexpr {
        sl_ast::VExpr::Ident(name, _) => dwarf_ctx.global_var(&name[..]).is_ok(),
        sl_ast::VExpr::OpApp(_, vexprs, _) | sl_ast::VExpr::FuncApp(_, vexprs, _) => {
            has_global(vexprs, dwarf_ctx)
        }
        _ => false,
    }
}

/// Helper function that determines if one of the sl_ast::VExprs from `vexprs`
/// is a global variable
pub fn has_global(vexprs: &Vec<sl_ast::VExpr>, dwarf_ctx: &DwarfCtx) -> bool {
    vexprs
        .iter()
        .fold(false, |acc, vexpr| acc || is_global(vexpr, dwarf_ctx))
}
