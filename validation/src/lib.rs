use wasm_parser::core::*;
use wasm_parser::Module;

type IResult<T> = Result<T, &'static str>;

type Expr = [Instruction];

mod extract;
pub mod instructions;

use extract::*;

use log::{debug, error};

#[derive(Debug, Clone)]
struct Context<'a> {
    types: Vec<&'a FuncType>,
    functions: Vec<FuncType>,
    tables: Vec<&'a TableType>,
    mems: Vec<&'a MemoryType>,
    global_entries: Vec<&'a GlobalVariable>,
    globals_ty: Vec<&'a GlobalType>,
    locals: Vec<()>,  //TODO
    labels: Vec<()>,  //TODO
    _return: Vec<()>, //TODO
}

pub fn validate(module: &Module) -> IResult<()> {
    let types = get_types(&module);
    let functions: Vec<IResult<_>> = get_funcs(&module)
        .iter()
        .map(|w| get_ty_of_function(&types, **w as usize))
        .collect();

    for f in functions.iter() {
        if f.is_err() {
            error!("Function {:?}", f);
            return Err("Function is not defined {:?}");
        }
    }

    let tables = get_tables(&module);
    let mems = get_mems(&module);
    let (global_entries, globals_ty) = get_globals(&module);

    let c = Context {
        types,
        functions: functions.into_iter().map(|w| w.unwrap()).collect(), //save because checked
        tables,
        mems,
        global_entries,
        globals_ty,
        locals: Vec::new(),
        labels: Vec::new(),
        _return: Vec::new(),
    };

    c.validate(&module)?;

    Ok(())
}

impl<'a> Context<'a> {
    pub fn get_c_prime(&self) -> Self {
        let copied = (&self.globals_ty).to_vec(); //TODO is this really copied?
        let copied2 = (&self.global_entries).to_vec(); //TODO is this really copied?

        Context {
            types: Vec::new(),
            functions: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            global_entries: copied2,
            globals_ty: copied,
            locals: Vec::new(),
            labels: Vec::new(),
            _return: Vec::new(),
        }
    }

    pub fn validate(&self, module: &Module) -> IResult<()> {
        let c_prime = self.get_c_prime().clone(); //TODO this might not be necessary

        // Check functype

        // -> https://webassembly.github.io/spec/core/valid/types.html#t-1-n-xref-syntax-types-syntax-functype-rightarrow-t-2-m

        // they are always valid
        debug!("Functypes are valid");

        // Check func

        // due to optimization, that has been already checked in top-level `validate`
        debug!("FunctionsTypes are valid");

        // Check table

        //https://webassembly.github.io/spec/core/valid/types.html#table-types

        // table tables are valid when the limit is in u32 range
        // that's statically guaranted
        debug!("TablesTypes are valid");

        // Check mem

        for mem in self.mems.iter() {
            check_memory_ty(mem)?;
        }

        debug!("MemoryTypes are valid");

        // Check global

        for entry in self.global_entries.iter() {
            // For each global under the Context C'

            let init = &entry.init;
            let init_expr_ty = get_expr_const_ty_global(init, &c_prime.globals_ty)?;

            if entry.ty.value_type != init_expr_ty {
                //Expr has not the same type as the global
                return Err("Expr has not the same type as the global");
            }
        }

        debug!("GlobalTypes are valid");

        // Check elem

        let elements = get_elemens(module);
        for elem in elements {
            check_elem_ty(elem, &self.tables, &self.types)?;
        }

        debug!("Elements are valid");

        // Check data

        let data = get_data(module);
        for d in data {
            check_data_ty(d, &self.mems)?;
        }

        debug!("Data is valid");

        // Start

        let start = get_start(module);

        if let Some(s) = start.get(0) {
            check_start(s, &self.types)?;
        }

        debug!("Start is valid");

        // Imports

        let imports = get_imports(module);
        for e in imports {
            check_import_ty(e, &self.types)?;
        }

        debug!("Imports are valid");

        // Check exports

        let exports = get_exports(module);
        for e in exports {
            check_export_ty(e, &self.types, &self.tables, &self.mems, &self.globals_ty)?;
        }

        debug!("Exports are valid");

        check_lengths(self)?;

        let exports = get_exports(module);
        check_export_names(&exports)?;

        Ok(())
    }
}

fn check_lengths(c: &Context) -> IResult<()> {
    // tables must not be larger than 1

    if c.tables.len() > 1 {
        return Err("Tables are larger than 1");
    }

    debug!("Table size is ok");

    // Memory must not be larger than 1

    if c.mems.len() > 1 {
        return Err("Memory are larger than 1");
    }

    Ok(())
}

/// All export names must be different
fn check_export_names(exports: &[&ExportEntry]) -> IResult<()> {
    let mut set = std::collections::HashSet::new();

    for e in exports.iter() {
        if !set.contains(&e.name) {
            set.insert(e.name.clone());
        } else {
            return Err("Export function names are not unique");
        }
    }

    debug!("Export names are unique");

    Ok(())
}

/// Evalutes the expr `init` and checks if it returns const
fn get_expr_const_ty_global(init: &Expr, globals_ty: &[&GlobalType]) -> IResult<ValueType> {
    use wasm_parser::core::NumericInstructions::*;
    use wasm_parser::core::VarInstructions::*;

    if init.is_empty() {
        return Err("No expr to evaluate");
    }

    match init.get(0).unwrap() {
        Instruction::Num(n) => match *n {
            OP_I32_CONST(_) => Ok(ValueType::I32),
            OP_I64_CONST(_) => Ok(ValueType::I64),
            OP_F32_CONST(_) => Ok(ValueType::F32),
            OP_F64_CONST(_) => Ok(ValueType::F64),
            _ => Err("Expression is not a const"),
        },
        Instruction::Var(n) => match *n {
            OP_GLOBAL_GET(lidx) => match globals_ty.get(lidx as usize).as_ref() {
                Some(global) => {
                    if global.mu == Mu::Var {
                        return Err("Global var is mutable");
                    }

                    Ok(global.value_type.clone())
                }
                None => Err("Global does not exist"),
            },
            _ => Err("Only Global get allowed"),
        },
        _ => Err("Wrong expression"),
    }
}

fn check_elem_ty(
    elem_ty: &ElementSegment,
    tables: &[&TableType],
    func_ty: &[&FuncType],
) -> IResult<bool> {
    //https://webassembly.github.io/spec/core/valid/modules.html#element-segments

    let table_idx = &elem_ty.index;
    let offset = &elem_ty.offset;
    let funcs_idx = &elem_ty.elems;

    if tables.get(*table_idx as usize).is_none() {
        return Err("No table defined for element's index");
    }

    get_expr_const_i32_ty(offset)?;

    // All function must be defined

    let not_def_funcs: Vec<_> = funcs_idx
        .iter()
        .filter_map(|w| func_ty.get(*w as usize))
        .collect();

    for f in not_def_funcs.iter() {
        error!("function is not defined {:?}", f);
    }

    if !not_def_funcs.is_empty() {
        return Err("Element section is not correct");
    }

    Ok(true)
}

/// Evalutes the expr `init` and checks if it returns const and I32
fn get_expr_const_i32_ty(init: &Expr) -> IResult<ValueType> {
    use wasm_parser::core::NumericInstructions::*;

    if init.is_empty() {
        return Err("No expr to evaluate");
    }

    match init.get(0).unwrap() {
        Instruction::Num(n) => match *n {
            OP_I32_CONST(_) => Ok(ValueType::I32),
            _ => Err("Expression is not a I32 const"),
        },
        _ => Err("Wrong expression"),
    }
}

fn check_data_ty(data_ty: &DataSegment, memtypes: &[&MemoryType]) -> IResult<bool> {
    //https://webassembly.github.io/spec/core/valid/modules.html#data-segments

    let mem_idx = data_ty.index;
    let offset = &data_ty.offset;

    if memtypes.get(mem_idx as usize).is_none() {
        panic!("Memory does not exist");
    }

    get_expr_const_i32_ty(&offset)?;

    Ok(true)
}

fn check_start(start: &StartSection, functypes: &[&FuncType]) -> IResult<bool> {
    //https://webassembly.github.io/spec/core/valid/modules.html#valid-start

    let fidx = start.index;

    if let Some(f) = functypes.get(fidx as usize).as_ref() {
        if !f.param_types.is_empty() && !f.return_types.is_empty() {
            error!("Function {:?}", f);
            return Err("Function is not a valid start function");
        }
    }

    Ok(true)
}

fn check_import_ty(import_ty: &ImportEntry, functypes: &[&FuncType]) -> IResult<bool> {
    check_import_desc(&import_ty.desc, functypes)
}

fn check_export_ty(
    export_ty: &ExportEntry,
    functypes: &[&FuncType],
    tabletypes: &[&TableType],
    memtypes: &[&MemoryType],
    globaltypes: &[&GlobalType],
) -> IResult<bool> {
    //https://webassembly.github.io/spec/core/valid/modules.html#exports

    macro_rules! exists(
        ($e:ident, $w:ident, $k:expr) => (
            match $e.get($w as usize).as_ref() {
                Some(_) => {Ok(true)}, //exists
                _ => Err($k)
            }
        )
    );

    match export_ty.kind {
        ExternalKindType::Function { ty } => exists!(functypes, ty, "Function does not exist"),
        ExternalKindType::Table { ty } => exists!(tabletypes, ty, "Table does not exist"),
        ExternalKindType::Memory { ty } => exists!(memtypes, ty, "Memory does not exist"),
        ExternalKindType::Global { ty } => exists!(globaltypes, ty, "Global does not exist"),
    }
}

// If there exists a `typeidx` in `types`, then `typeidx` has its type.
fn get_ty_of_function(types: &[&FuncType], typeidx: usize) -> IResult<FuncType> {
    if let Some(t) = types.get(typeidx) {
        return Ok(FuncType {
            param_types: t.param_types.clone(),
            return_types: t.return_types.clone(),
        });
    }

    Err("No function with this index")
}

fn check_import_desc(e: &ImportDesc, types: &[&FuncType]) -> IResult<bool> {
    let b = match e {
        ImportDesc::Function { ty } => get_ty_of_function(types, *ty as usize).is_ok(),
        ImportDesc::Table { .. } => true, //Limits are u32 that's why they are valid
        ImportDesc::Memory { ty } => check_memory_ty(&ty)?,
        ImportDesc::Global { .. } => true, // this is true, because `mut` is always correct and `valuetype` was correctly parsed
    };

    Ok(b)
}

fn check_memory_ty(memory: &MemoryType) -> IResult<bool> {
    let b = match memory.limits {
        Limits::Zero(n) => n < 2u32.checked_pow(16).unwrap(), //cannot overflow
        Limits::One(n, m) => n < 2u32.checked_pow(16).unwrap() && m < 2u32.checked_pow(16).unwrap(), //cannot overflow
    };

    Ok(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic("Export Functions are not unique")]
    fn test_duplicated_export_entries() {
        let k = ExportSection {
            entries: vec![
                ExportEntry {
                    name: "test1".to_string(),
                    kind: ExternalKindType::Function { ty: 0 },
                },
                ExportEntry {
                    name: "test1".to_string(),
                    kind: ExternalKindType::Function { ty: 1 },
                },
            ],
        };

        //TODO if this is a requirement too?
        let w = FunctionSection { types: vec![0, 1] };

        let t = TypeSection {
            entries: vec![FuncType::empty(), FuncType::empty()],
        };

        let module = Module {
            sections: vec![Section::Type(t), Section::Function(w), Section::Export(k)],
        };

        validate(&module).unwrap();
    }

    /*
    #[test]
    fn test_check_limits() {
        let l = Limits::One(10, 20);
        let l2 = Limits::Zero(10);

        assert!(check_limits(&l, 15));
        assert!(check_limits(&l2, 15));

        assert_eq!(false, check_limits(&l, 9));
        assert_eq!(false, check_limits(&l2, 9));
        assert_eq!(false, check_limits(&l, 21));
    }*/
}
