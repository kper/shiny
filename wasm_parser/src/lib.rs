#![allow(clippy::same_item_push)]
#![feature(buf_read_has_data_left)]

extern crate log;

use log::debug;

pub mod core;
mod instructions;
mod leb128;

use self::core::*;
use self::leb128::*;

use anyhow::Result;
use byteorder::{ByteOrder, LittleEndian};
use serde::{Deserialize, Serialize};

use std::io::prelude::*;
use std::io::BufReader;

pub const MAGIC_NUMBER: &[u8] = &[0, 97, 115, 109];
const END_INSTR: [u8; 1] = [0x0B];

#[derive(Debug, Serialize, Deserialize)]
pub struct Module {
    pub sections: Vec<Section>,
}

#[macro_export]
macro_rules! read_wasm {
    ($fs_name:expr) => {{
        use std::fs::File;
        use std::io::prelude::*;

        let mut fs = File::open($fs_name).unwrap();
        let mut reader = Vec::new();

        fs.read_to_end(&mut reader).unwrap();

        reader
    }};
}

#[macro_export]
macro_rules! consume {
    ($reader:expr, $num:expr) => {{
        use std::io::prelude::*;
        let mut tmp = vec![0u8; $num as usize];
        debug!("Consuming {} bytes", $num);
        $reader.read_exact(&mut tmp).unwrap();

        tmp
    }};
}

#[macro_export]
macro_rules! consume_byte {
    ($reader:expr) => {{
        use std::io::prelude::*;
        let mut tmp: [u8; 1] = [0u8; 1];
        $reader.read_exact(&mut tmp).unwrap();

        tmp
    }};
}

#[macro_export]
macro_rules! consume_up_to {
    ($reader:expr, $num:expr) => {{
        use std::io::prelude::*;
        let mut tmp = vec![0u8; $num as usize];
        let _ = $reader.read(&mut tmp).expect("Reading bytes failed");

        tmp
    }};
}

#[macro_export]
macro_rules! read {
    ($reader:expr, $num:expr) => {{
        use std::io::prelude::*;
        debug!("Reading {} bytes", $num);
        &$reader.fill_buf().expect("Cannot read from the buffer")[0..($num as usize)]
    }};
}

type Bytes<'a> = &'a [u8];
type BytesReader<'a> = BufReader<Bytes<'a>>;

/// Parses a vector of bytes into a webassembly module.
pub fn parse(content: Bytes) -> Result<Module> {
    let buf_reader = BufReader::new(content);

    let sections = parse_module(buf_reader).expect("Parsing failed");

    Ok(Module { sections })
}

fn parse_module(mut i: BytesReader) -> Result<Vec<Section>> {
    let magic = take_magic_number(&mut i)?;

    assert_eq!(MAGIC_NUMBER, magic);

    let _version = take_version_number(&mut i)?;

    let mut sections = Vec::new();
    while i.has_data_left().is_ok() {
        let section = parse_section(&mut i)?;
        sections.push(section);
    }

    Ok(sections)
}

fn parse_section(i: &mut BytesReader) -> Result<Section> {
    let n = consume_byte!(i);
    let size = take_leb_u32(i)?;
    let mut counter = Counter::default();

    debug!("SECTION {:?} {:?}", n, size);

    let m = match n[0] {
        0 => parse_custom_section(i, size)?,
        1 => parse_type_section(i, size)?,
        2 => parse_import_section(i, size)?,
        3 => parse_function_section(i, size)?,
        4 => parse_table_section(i, size)?,
        5 => parse_memory_section(i, size)?,
        6 => parse_global_section(i, size, &mut counter)?,
        7 => parse_export_section(i, size)?,
        8 => parse_start_section(i, size)?,
        9 => parse_element_section(i, size, &mut counter)?,
        10 => parse_code_section(i, size, &mut counter)?,
        11 => parse_data_section(i, size, &mut counter)?,
        _ => anyhow::bail!("invalid section id"),
    };

    Ok(m)
}

fn take_magic_number(reader: &mut BytesReader) -> Result<Vec<u8>> {
    debug!("take_until_magic_number");
    Ok(consume!(reader, 4u32))
}

fn take_version_number(reader: &mut BytesReader) -> Result<Vec<u8>> {
    debug!("take_version_number");
    Ok(consume!(reader, 4u32))
}

fn parse_custom_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse custom section");
    let name = take_name(i)?;

    Ok(Section::Custom(CustomSection { name }))
}

fn parse_type_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse type section");

    let times = take_leb_u32(i)?;
    let mut signatures = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let sig = take_function_signature(i)?;
        signatures.push(sig);
    }

    Ok(Section::Type(TypeSection {
        entries: signatures,
    }))
}

fn parse_import_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse import section");
    let times = take_leb_u32(i)?;
    let mut imports = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let import = take_import(i)?;
        imports.push(import);
    }

    Ok(Section::Import(ImportSection { entries: imports }))
}

fn parse_function_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse function section");
    let times = take_leb_u32(i)?;
    let mut functions = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let function = take_leb_u32(i)?;
        functions.push(function);
    }

    Ok(Section::Function(FunctionSection { types: functions }))
}

fn parse_table_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse table function");
    let times = take_leb_u32(i)?;
    let mut tables = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let table = take_tabletype(i)?;
        tables.push(table);
    }

    Ok(Section::Table(TableSection { entries: tables }))
}

fn parse_memory_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse memory function");
    let times = take_leb_u32(i)?;
    let mut mems = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let mem = take_memtype(i)?;
        mems.push(mem);
    }

    Ok(Section::Memory(MemorySection { entries: mems }))
}

fn parse_global_section<'a, 'b>(
    i: &mut BytesReader,
    _size: u32,
    counter: &'b mut Counter,
) -> Result<Section> {
    debug!("parse global function");
    let times = take_leb_u32(i)?;
    let mut globals = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let global = take_global(i, counter)?;
        globals.push(global);
    }

    Ok(Section::Global(GlobalSection { globals }))
}

fn parse_export_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse export function");
    let times = take_leb_u32(i)?;
    let mut exports = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let export = take_export(i)?;
        exports.push(export);
    }

    Ok(Section::Export(ExportSection { entries: exports }))
}

fn parse_start_section(i: &mut BytesReader, _size: u32) -> Result<Section> {
    debug!("parse start function");
    let func_idx = take_leb_u32(i)?;

    Ok(Section::Start(StartSection { index: func_idx }))
}

fn parse_element_section<'b>(
    i: &mut BytesReader,
    _size: u32,
    counter: &'b mut Counter,
) -> Result<Section> {
    debug!("parse_element_section");
    let times = take_leb_u32(i)?;
    let mut elements = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let elem = take_elem(i, counter)?;
        elements.push(elem);
    }

    Ok(Section::Element(ElementSection { entries: elements }))
}

fn parse_data_section<'b>(
    i: &mut BytesReader,
    _size: u32,
    counter: &'b mut Counter,
) -> Result<Section> {
    debug!("parse_data_section");
    let times = take_leb_u32(i)?;
    let mut entries = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let data = take_data(i, counter)?;
        entries.push(data);
    }

    Ok(Section::Data(DataSection { entries }))
}

fn parse_code_section<'a, 'b>(
    i: &mut BytesReader,
    _size: u32,
    counter: &'b mut Counter,
) -> Result<Section> {
    debug!("parse_code_section");

    let times = take_leb_u32(i)?;
    let mut codes = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let code = take_code(i, counter)?;
        codes.push(code);
    }

    Ok(Section::Code(CodeSection { entries: codes }))
}

fn take_code<'b>(i: &mut BytesReader, counter: &'b mut Counter) -> Result<FunctionBody> {
    debug!("parse_code");

    let _size = take_leb_u32(i)?;
    let k = take_func(i, counter)?;

    Ok(k)
}

fn take_func<'b>(i: &mut BytesReader, counter: &'b mut Counter) -> Result<FunctionBody> {
    debug!("take_func");

    let times = take_leb_u32(i)?;
    let mut locals = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let local = take_local(i)?;
        locals.push(local);
    }

    debug!("locals {:?}", locals);

    let code = take_expr(i, counter)?;

    Ok(FunctionBody {
        locals,
        code: InstructionWrapper::wrap_instructions(counter, code),
    })
}

fn take_local(i: &mut BytesReader) -> Result<LocalEntry> {
    debug!("take_local");

    let n = take_leb_u32(i)?;
    let t = take_valtype(i)?;

    Ok(LocalEntry { count: n, ty: t })
}

fn take_data<'a, 'b>(i: &mut BytesReader, counter: &'b mut Counter) -> Result<DataSegment> {
    debug!("take_data");

    let mem_idx = take_leb_u32(i)?;
    let e = take_expr(i, counter)?;

    let times = take_leb_u32(i)?;
    let b = consume!(i, times as usize);

    Ok(DataSegment {
        data: mem_idx,
        offset: InstructionWrapper::wrap_instructions(counter, e),
        init: b,
    })
}

fn take_elem<'a, 'b>(i: &mut BytesReader, counter: &'b mut Counter) -> Result<ElementSegment> {
    debug!("take_elem");

    let table_idx = take_leb_u32(i)?;
    let e = take_expr(i, counter)?;
    let times = take_leb_u32(i)?;
    let mut y_vec = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let num = take_leb_u32(i)?;
        y_vec.push(num);
    }

    Ok(ElementSegment {
        table: table_idx,
        offset: InstructionWrapper::wrap_instructions(counter, e),
        init: y_vec,
    })
}

fn take_export(i: &mut BytesReader) -> Result<ExportEntry> {
    debug!("take_export");

    let name = take_name(i)?;
    let kind = take_desc(i)?;

    Ok(ExportEntry { name, kind })
}

fn take_global<'a, 'b>(i: &mut BytesReader, counter: &'b mut Counter) -> Result<GlobalVariable> {
    let ty = take_globaltype(i)?;
    let e = take_expr(i, counter)?;

    Ok(GlobalVariable {
        ty,
        init: InstructionWrapper::wrap_instructions(counter, e),
    })
}

pub(crate) fn take_expr<'b>(
    i: &mut BytesReader,
    counter: &'b mut Counter,
) -> Result<Vec<Instruction>> {
    debug!("take expr");

    let mut instructions = Vec::new();

    loop {
        let k = consume_byte!(i);

        if k == END_INSTR {
            break;
        }

        let instruction = instructions::parse_instr(i, counter)?;
        instructions.push(instruction);
    }

    let e = consume_byte!(i); //0x0B
    assert_eq!(e, END_INSTR);

    Ok(instructions)
}

fn take_import(i: &mut BytesReader) -> Result<ImportEntry> {
    debug!("take_import");

    let module_name = take_name(i)?;
    let name = take_name(i)?;
    let desc = take_import_desc(i)?;

    Ok(ImportEntry {
        module_name,
        name,
        desc,
    })
}

fn take_import_desc(i: &mut BytesReader) -> Result<ImportDesc> {
    debug!("take_desc");

    let b = consume_byte!(i);

    let desc = match b[0] {
        0x00 => {
            let t = take_leb_u32(i)?;
            ImportDesc::Function { ty: t }
        }
        0x01 => {
            let t = take_tabletype(i)?;
            ImportDesc::Table { ty: t }
        }
        0x02 => {
            let t = take_memtype(i)?;
            ImportDesc::Memory { ty: t }
        }
        0x03 => {
            let t = take_globaltype(i)?;
            ImportDesc::Global { ty: t }
        }
        _ => anyhow::bail!("desc failed"),
    };

    Ok(desc)
}

fn take_desc(i: &mut BytesReader) -> Result<ExternalKindType> {
    debug!("take_desc");

    let b = consume!(i, 1u8);

    let desc = match b[0] {
        0x00 => {
            let t = take_leb_u32(i)?;
            ExternalKindType::Function { ty: t }
        }
        0x01 => {
            let t = take_leb_u32(i)?;
            ExternalKindType::Table { ty: t }
        }
        0x02 => {
            let t = take_leb_u32(i)?;
            ExternalKindType::Memory { ty: t }
        }
        0x03 => {
            let t = take_leb_u32(i)?;
            ExternalKindType::Global { ty: t }
        }
        _ => anyhow::bail!("desc failed"),
    };

    Ok(desc)
}

fn take_memtype(i: &mut BytesReader) -> Result<MemoryType> {
    debug!("take_memtype");
    let l = take_limits(i)?;

    Ok(MemoryType { limits: l })
}

fn take_tabletype(i: &mut BytesReader) -> Result<TableType> {
    debug!("take_tabletype");
    let element_type = consume_byte!(i);
    assert_eq!(0x70, element_type[0]);
    let limits = take_limits(i)?;

    Ok(TableType {
        element_type: 0x70,
        limits,
    })
}

fn take_globaltype(i: &mut BytesReader) -> Result<GlobalType> {
    debug!("take_globaltype");
    let val = take_valtype(i)?;
    let b = consume_byte!(i);

    let mu = match b[0] {
        0x00 => Mu::Const,
        0x01 => Mu::Var,
        _ => panic!("wrong mu"),
    };

    Ok(GlobalType {
        value_type: val,
        mu,
    })
}

fn take_limits(i: &mut BytesReader) -> Result<Limits> {
    debug!("take_limits");
    let n = consume_byte!(i);

    Ok(match n[0] {
        0x00 => {
            let n = take_leb_u32(i)?;

            Limits::Zero(n)
        }
        0x01 => {
            let n = take_leb_u32(i)?;
            let m = take_leb_u32(i)?;

            Limits::One(n, m)
        }
        _ => anyhow::bail!("Limit has wrong tag"),
    })
}

fn take_function_signature(i: &mut BytesReader) -> Result<FunctionSignature> {
    debug!("take_function_signature");

    let offset = consume_byte!(i); //0x60

    assert_eq!(offset[0], 0x60);

    let times = take_leb_u32(i)?;
    let t1 = consume!(i, times);
    let times = take_leb_u32(i)?;
    let t2 = consume!(i, times);

    let param_types: Vec<_> = t1.into_iter().map(|w| w.into()).collect();
    let return_types: Vec<_> = t2.into_iter().map(|w| w.into()).collect();

    Ok(FunctionSignature {
        param_types,
        return_types,
    })
}

fn take_valtype(i: &mut BytesReader) -> Result<ValueType> {
    debug!("take_valtype");
    let n = consume!(i, 1u8);

    Ok(n[0].into())
}

fn take_blocktype(i: &mut BytesReader) -> Result<BlockType> {
    debug!("take_blocktype");
    let n = consume!(i, 1u8);

    let bty = match n[0] {
        0x40 => BlockType::Empty,
        0x7F | 0x7E | 0x7D | 0x7C => BlockType::ValueType(n[0].into()),
        _ => {
            // This must be signed 33 bit
            // Weird, Page 96 spec
            let k = take_leb_i33(i)?;

            BlockType::FuncTy(k as i32)
        }
    };

    Ok(bty)
}

pub(crate) fn take_f32(i: &mut BytesReader) -> Result<f32> {
    debug!("take_f32");
    let bytes = consume!(i, 4u8);

    Ok(LittleEndian::read_f32(&bytes))
}

pub(crate) fn take_f64(i: &mut BytesReader) -> Result<f64> {
    debug!("take_f64");
    let bytes = consume!(i, 8u8);

    Ok(LittleEndian::read_f64(&bytes))
}

fn take_name(i: &mut BytesReader) -> Result<String> {
    debug!("take_name");
    let times = take_leb_u32(i)?;
    let bytes = consume!(i, times);

    Ok(String::from_utf8(bytes).unwrap())
}

macro_rules! take_leb {
    ($function:ident, $reader:expr, $buffer_len:expr) => {{
        let length = $reader.fill_buf().unwrap().len();
        let buffer_len = $buffer_len as usize;
        debug!("Remaining is {}", length);
        debug!("Required is {}", buffer_len);

        // Find out whether enough bytes are remaining
        let threshold_buffer_len = if length < buffer_len {
            length
        } else {
            buffer_len
        };

        // Read them, but do not consume them
        let bytes: &[u8] = read!($reader, threshold_buffer_len);

        // leb.1 saves the amount of bytes which were really required
        let leb = $function(&bytes[..]);

        // Read them from the reader
        let _ = consume!($reader, leb.1);
        Ok(leb.0)
    }};
}

pub(crate) fn take_leb_u32(i: &mut BytesReader) -> Result<u32> {
    debug!("take_leb_u32");
    take_leb!(read_u32_leb128, i, 5u8)
}

pub(crate) fn take_leb_i32(i: &mut BytesReader) -> Result<i32> {
    debug!("take_leb_i32");
    take_leb!(read_i32_leb128, i, 5u8)
}

pub(crate) fn take_leb_i64(i: &mut BytesReader) -> Result<i64> {
    debug!("take_leb_i64");
    take_leb!(read_i64_leb128, i, 10u8)
}

pub(crate) fn take_leb_i33(i: &mut BytesReader) -> Result<i64> {
    debug!("take_leb_i33");
    take_leb!(read_i33_leb128, i, 6u8)
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;

    macro_rules! test_file {
        ($fs_name:expr) => {
            let file = read_wasm!(&format!("test_files/{}", $fs_name));
            let ast = parse(&file).unwrap();
            assert_snapshot!($fs_name, format!("{:#?}", ast));
        };
    }

    macro_rules! test_template {
        ($fname:ident, $input:expr, $expected:expr) => {
            let n = take_leb_i32(&mut BufReader::new(&$input)).unwrap();
            assert_eq!(n as i128, $expected);
        };
    }

    #[test]
    fn should_consume_one_byte_with_consume() {
        let bytes = [5u8; 10];
        let mut reader = std::io::BufReader::new(bytes.as_slice());
        let buffer = consume!(&mut reader, 1);
        assert_eq!(buffer.len(), 1);
        assert_eq!(*buffer.get(0).unwrap(), 5u8);
    }

    #[test]
    fn test_take_leb_i32() {
        env_logger::init();
        let bytes = [0x7f, 0, 0, 0];
        let expected = -1;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i33() {
        let bytes = [0x7f, 0, 0, 0];
        let expected = -1;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i64() {
        let bytes = [0x7f, 0, 0, 0];
        let expected = -1;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i64_2() {
        let bytes = [0x3c, 0, 0, 0];
        let expected = 0x3c;

        test_template!(take_leb_i64, bytes, expected);
    }

    #[test]
    fn test_take_leb_i64_3() {
        let bytes = [0x80, 0x7f];
        let expected = -120;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_u32_n135() {
        let bytes = [135u8, 0x01];
        let expected = 135;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i32_n8192() {
        let bytes = [0x80, 0xc0, 0x00];
        let expected = 8192;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i32_neg_n8192() {
        let bytes = [0x80, 0x40];
        let expected = -8192;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i64_n8192() {
        let bytes = [0x80, 0xc0, 0x00];
        let expected = 8192;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i64_neg_n8192() {
        let bytes = [0x80, 0x40];
        let expected = -8192;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_take_leb_i64_min() {
        let bytes = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f];
        let expected: i128 = -9223372036854775808;

        test_template!(take_leb_i32, bytes, expected);
    }

    #[test]
    fn test_empty_wasm() {
        env_logger::init();
        test_file!("empty.wasm");
    }

    #[test]
    fn test_return_i32() {
        test_file!("return_i32.wasm");
    }

    #[test]
    fn test_return_i64() {
        test_file!("return_i64.wasm");
    }

    #[test]
    fn test_function_call() {
        test_file!("function_call.wasm");
    }

    #[test]
    fn test_arithmetic() {
        test_file!("arithmetic.wasm");
    }

    #[test]
    fn test_block_add_i32() {
        test_file!("block_add_i32.wasm");
    }

    #[test]
    fn test_loop_mult() {
        test_file!("loop_mult.wasm");
    }

    #[test]
    fn test_unreachable() {
        test_file!("unreachable.wasm");
    }

    #[test]
    fn test_if_loop() {
        test_file!("if_loop.wasm");
    }

    #[test]
    fn test_logic() {
        test_file!("logic.wasm");
    }

    #[test]
    fn test_gcd() {
        test_file!("gcd.wasm");
    }

    #[test]
    fn test_as_loop_mid_br_if() {
        //env_logger::init();
        test_file!("as_loop_mid_br_if.wasm");
    }

    #[test]
    fn test_global() {
        test_file!("global.wasm");
    }
}
