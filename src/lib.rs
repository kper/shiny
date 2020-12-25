#[macro_use]
extern crate log;
extern crate wasm_parser;
pub mod allocation;
pub mod config;
pub mod debugger;
pub mod engine;
pub mod instantiation;
mod operations;
mod page;
pub mod value;
pub mod cli;

pub use validation::validate;
pub use wasm_parser::parse;
pub use wasm_parser::read_wasm;

pub(crate) const PAGE_SIZE: usize = 65536;

#[cfg(test)]
mod tests;

use debugger::ProgramCounter;
use debugger::RelativeProgramCounter;
use engine::*;

#[allow(unused_macros)]
#[macro_export]
macro_rules! construct_engine {
    ($body:expr, $params:expr, $returns:expr) => {{
        #[allow(unused_imports)]
        use wasm_parser::core::Instruction::*;
        use wasm_parser::core::*;

        let mut e = crate::empty_engine();

        let body = FunctionBody {
            locals: vec![],
            code: $body,
        };

        e.store.funcs = vec![FuncInstance {
            ty: FunctionSignature {
                param_types: $params,
                return_types: $returns,
            },
            code: body.clone(),
        }];

        // Set the code section
        e.module.code = vec![body.clone()];

        // Export the function
        e.module.funcaddrs.push(0);
        e.module.exports = vec![ExportInstance {
            name: "test".to_string(),
            value: ExternalKindType::Function { ty: 0 },
        }];

        e
    }};
}
