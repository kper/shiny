use crate::engine::Engine;
use crate::engine::StackContent;
use crate::value::Value::I32;
use crate::PAGE_SIZE;
use anyhow::{Context, Result};

impl Engine {
    pub(crate) fn memory_size(&mut self) -> Result<()> {
        let module = &self.module_instance;
        let addr = module
            .lookup_memory_addr(&0)
            .context("No memory address found")?;
        let instance = &self.store.memory[addr.get()];

        let sz = instance.data.len() / PAGE_SIZE;

        self.store.stack.push(StackContent::Value(I32(sz as i32)));

        Ok(())
    }
}
