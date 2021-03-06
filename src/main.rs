#[macro_use]
extern crate log;
extern crate env_logger;
extern crate funky;
extern crate regex;

use docopt::Docopt;
use funky::cli::parse_args;
use funky::debugger::RelativeProgramCounter;
use funky::engine::module::ModuleInstance;
use funky::engine::Engine;
use funky::engine::import_resolver::Imports;
use serde::Deserialize;
use validation::validate;
use wasm_parser::{parse, read_wasm};

const USAGE: &str = "
Funky - a WebAssembly Interpreter

Usage:
  ./funky <input> <function> [<args>...] [--stage0 | --stage1] [--spec] [--debugger]
  ./funky (-h | --help)
  ./funky --version

Options:
  -h --help     Show this screen.
  --version     Show version.
  --stage0      Stop at Parser.
  --stage1      Stop at Validation.
  --spec        Format output to be compliant for spec tests";

#[derive(Debug, Deserialize)]
struct Args {
    flag_stage0: bool,
    flag_stage1: bool,
    flag_spec: bool,
    arg_input: String,
    arg_function: String,
    arg_args: Vec<String>,
}

fn main() {
    env_logger::init();

    let args: Args = Docopt::new(USAGE)
        .and_then(|d| d.deserialize())
        .unwrap_or_else(|e| e.exit());

    let reader = read_wasm!(args.arg_input);

    info!("Parsing wasm file");

    let module = parse(reader).unwrap();

    if args.flag_stage0 {
        println!("{:#?}", module);

        return;
    }

    let validation = validate(&module);

    if args.flag_stage1 {
        println!("{:#?}", validation);

        return;
    }

    let (mi, functions) = ModuleInstance::new(&module);
    info!("Constructing engine");

    let e = Engine::new(
        mi,
        &functions,
        &module,
        Box::new(RelativeProgramCounter::default()),
        &Imports::new(),
    );
    debug!("engine {:#?}", e);

    debug!("Instantiation engine");

    if let Err(err) = e {
        eprintln!("ERROR: {}", err);
        err.chain()
            .skip(1)
            .for_each(|cause| eprintln!("because: {}", cause));
        std::process::exit(1);
    }

    let mut engine = e.unwrap();

    let inv_args = parse_args(args.arg_args);

    if let Err(err) = engine.invoke_exported_function_by_name(&args.arg_function, inv_args) {
        eprintln!("ERROR: {}", err);
        err.chain()
            .skip(1)
            .for_each(|cause| eprintln!("because: {}", cause));
        std::process::exit(1);
    }

    if engine.store.stack.last().is_some() {
        let value = engine.store.stack.pop();
        println!("{:?}", value);
    }
}
