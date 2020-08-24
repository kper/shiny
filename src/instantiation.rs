use crate::engine::*;
use wasm_parser::Module;
use crate::value::Value;

use anyhow::{anyhow, Result};

type StartFunctionAddr = u32;

/// Returns the addr of the start function, which needs to be invoked
pub fn instantiation(
    m: &Module,
    mod_instance: &ModuleInstance,
    store: &mut Store,
) -> Result<Option<StartFunctionAddr>> {
    // Step 1

    // Module is already valid, because checked before

    // ... skip to Step 7 TODO

    // Step 7

    let frame = Frame {
        locals: Vec::new(),
        arity: 0,
        //module_instance: Rc::downgrade(&mod_instance),
    };

    // Step 8

    store.stack.push(StackContent::Frame(frame));

    // Step 9 and Step 13
    if let Err(err) = instantiate_elements(m, mod_instance, store) {
        return Err(anyhow!("{}", err));
    }

    // Step 10 and Step 14
    if let Err(err) = instantiate_data(m, mod_instance, store) {
        return Err(anyhow!("{}", err));
    }

    // Step 11 and 12
    if let Some(StackContent::Frame(f)) = store.stack.pop() {
        let frame = Frame {
            locals: Vec::new(),
            arity: 0,
            //module_instance: Rc::downgrade(&mod_instance),
        };

        assert_eq!(frame, f);
    } else {
        return Err(anyhow!("No frame on the stack"));
    }

    // Step 15

    let start_func = instantiate_start(m, mod_instance, store)?;

    Ok(start_func)
}

fn instantiate_elements(
    m: &Module,
    mod_instance: &ModuleInstance,
    store: &mut Store,
) -> Result<()> {
    debug!("instantiate elements");

    let ty = validation::extract::get_elemens(&m);

    for e in ty.iter() {
        let eoval = crate::allocation::get_expr_const_ty_global(&e.offset)
            .map_err(|_| anyhow!("Fetching const expr failed"))?;

        if let Value::I32(table_index) = eoval {
            //table_index = eo_i

            let borrow = &mod_instance;

            let table_addr = borrow
                .tableaddrs
                .get(table_index as usize)
                .ok_or_else(|| anyhow!("Table index does not exists"))?;

            let table_inst = store
                .tables
                .get_mut(*table_addr as usize)
                .ok_or_else(|| anyhow!("Table addr does not exists"))?;

            let eend = table_index + e.init.len() as i32;

            if eend > table_inst.elem.len() as i32 {
                return Err(anyhow!("eend is larger than table_inst.elem"));
            }

            // Step 13

            for (j, funcindex) in e.init.iter().enumerate() {
                use std::mem::replace;

                let funcaddr = borrow
                    .funcaddrs
                    .get(*funcindex as usize)
                    .ok_or_else(|| anyhow!("No function with funcindex"))?;

                let _ = replace(
                    &mut table_inst.elem[table_index as usize + j],
                    Some(*funcaddr),
                );
            }
        } else {
            panic!("Assertion failed. Element's offset is not I32");
        }
    }

    Ok(())
}

fn instantiate_data(
    m: &Module,
    mod_instance: &ModuleInstance,
    store: &mut Store,
) -> Result<()> {
    debug!("instantiate elements");

    let ty = validation::extract::get_data(&m);

    for data in ty.iter() {
        debug!("data offset {:?}", data.offset);

        let doval = crate::allocation::get_expr_const_ty_global(&data.offset)
            .map_err(|_| anyhow!("Fetching const expr failed"))?;

        if let Value::I32(mem_idx) = doval {
            debug!("Memory index is {}", mem_idx);

            //mem_idx = do_i
            let borrow = &mod_instance;
            let mem_addr = borrow
                .memaddrs
                .get(0)
                .ok_or_else(|| anyhow!("Memory index does not exists"))?;

            debug!("Memory addr is {}", mem_addr);

            let mem_inst = store
                .memory
                .get_mut(*mem_addr as usize)
                .ok_or_else(|| anyhow!("Memory addr does not exists"))?;

            let dend = mem_idx + data.init.len() as i32;

            if dend > mem_inst.data.len() as i32 {
                return Err(anyhow!("dend is larger than mem_inst.data"));
            }

            // Step 14

            use std::mem::replace;
            for (j, b) in data.init.iter().enumerate() {
                let _ = replace(&mut mem_inst.data[mem_idx as usize + j], *b);
            }
        }
    }

    Ok(())
}

fn instantiate_start(
    m: &Module,
    mod_instance: &ModuleInstance,
    store: &mut Store,
) -> Result<Option<u32>> {
    debug!("instantiate start");

    if let Some(start_section) = validation::extract::get_start(m).first() {
        debug!("Start section {:#?}", start_section);

        let borrow = &mod_instance;
        let func_addr = borrow
            .funcaddrs
            .get((start_section.index) as usize)
            .ok_or_else(|| anyhow!("got no func_addr"))?;

        // Check if the functions really exists
        let _func_instance = store
            .funcs
            .get(*func_addr as usize)
            .ok_or_else(|| anyhow!("Function does not exist"))?;

        return Ok(Some(*func_addr));
    } else {
        debug!("No start section");
    }

    Ok(None)
}
