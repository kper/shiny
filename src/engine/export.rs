use wasm_parser::core::{ExportEntry, ExternalKindType};

#[derive(Debug, Clone, PartialEq)]
pub struct ExportInstance {
    pub name: String,
    pub value: ExternalKindType,
}

impl From<&ExportEntry> for ExportInstance {
    fn from(state: &ExportEntry) -> ExportInstance {
        ExportInstance {
            name: state.name.clone(),
            value: state.kind,
        }
    }
}
