#![allow(clippy::same_item_push)]

extern crate log;

use log::debug;

pub mod core;
mod instructions;
mod leb128;

use self::core::*;
use self::leb128::*;

use anyhow::Result;
use byteorder::{ByteOrder, LittleEndian};
use nom::bytes::complete::take;
use nom::combinator::complete;
use nom::multi::{count, many0};
use nom::IResult;
use serde::{Deserialize, Serialize};

pub const MAGIC_NUMBER: &[u8] = &[0, 97, 115, 109];
const END_INSTR: &[u8] = &[0x0B];

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

pub fn parse(content: Vec<u8>) -> Result<Module> {
    let slice = content.as_slice();

    let parsed = parse_module(slice).expect("Parsing failed");

    let (_, sections) = parsed;
    Ok(Module { sections })
}

fn parse_module(i: &[u8]) -> IResult<&[u8], Vec<Section>> {
    let (i, magic) = take_until_magic_number(i)?;

    assert_eq!(MAGIC_NUMBER, magic);

    let (i, _version) = take_version_number(i)?;

    let s = complete(many0(parse_section));

    let (i, k) = s(i)?;

    Ok((i, k))
}

fn parse_section(i: &[u8]) -> IResult<&[u8], Section> {
    let (i, n) = take(1u8)(i)?;
    let (i, size) = take_leb_u32(i)?;
    let mut counter = Counter::default();

    debug!("SECTION {:?} {:?}", n, size);

    let (i, m) = match n[0] {
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
        _ => panic!("invalid section id"),
    };

    Ok((i, m))
}

fn take_until_magic_number(i: &[u8]) -> IResult<&[u8], &[u8]> {
    debug!("take_until_magic_number");
    take(4u8)(i)
}

fn take_version_number(i: &[u8]) -> IResult<&[u8], &[u8]> {
    debug!("take_version_number");
    take(4u8)(i)
}

fn parse_custom_section(i: &[u8], size: u32) -> IResult<&[u8], Section> {
    debug!("parse custom section");
    let (k, name) = take_name(i)?;

    let str_len = i.len() - k.len();

    let (i, _) = take(size as usize - str_len)(k)?; //consume empty bytes

    Ok((i, Section::Custom(CustomSection { name })))
}

fn parse_type_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse type section");

    let (i, times) = take_leb_u32(i)?;
    let (i, vec) = count(take_function_signature, times as usize)(i)?;

    Ok((i, Section::Type(TypeSection { entries: vec })))
}

fn parse_import_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse import section");
    let (i, times) = take_leb_u32(i)?;
    let (i, import) = count(take_import, times as usize)(i)?;

    Ok((i, Section::Import(ImportSection { entries: import })))
}

fn parse_function_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse function section");
    let (i, times) = take_leb_u32(i)?;
    let (i, functions) = count(take_leb_u32, times as usize)(i)?;

    Ok((i, Section::Function(FunctionSection { types: functions })))
}

fn parse_table_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse table function");
    let (i, times) = take_leb_u32(i)?;
    let (i, tables) = count(take_tabletype, times as usize)(i)?;

    Ok((i, Section::Table(TableSection { entries: tables })))
}

fn parse_memory_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse memory function");
    let (i, times) = take_leb_u32(i)?;
    let (i, mem) = count(take_memtype, times as usize)(i)?;

    Ok((i, Section::Memory(MemorySection { entries: mem })))
}

fn parse_global_section<'a, 'b>(
    i: &'a [u8],
    _size: u32,
    counter: &'b mut Counter,
) -> IResult<&'a [u8], Section> {
    debug!("parse global function");
    let (mut i, times) = take_leb_u32(i)?;
    let mut globals = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let k = take_global(i, counter)?;
        i = k.0;
        globals.push(k.1);
    }

    Ok((i, Section::Global(GlobalSection { globals })))
}

fn parse_export_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse export function");
    let (i, times) = take_leb_u32(i)?;
    let (i, entries) = count(take_export, times as usize)(i)?;

    Ok((i, Section::Export(ExportSection { entries })))
}

fn parse_start_section(i: &[u8], _size: u32) -> IResult<&[u8], Section> {
    debug!("parse start function");
    let (i, func_idx) = take_leb_u32(i)?;

    Ok((i, Section::Start(StartSection { index: func_idx })))
}

fn parse_element_section<'a, 'b>(
    i: &'a [u8],
    _size: u32,
    counter: &'b mut Counter,
) -> IResult<&'a [u8], Section> {
    debug!("parse_element_section");
    let (mut i, times) = take_leb_u32(i)?;
    //let (i, elements) = count(take_elem, times as usize)(i)?;
    let mut elements = Vec::with_capacity(times as usize);

    for _ in 0..times {
        let k = take_elem(i, counter)?;
        i = k.0;
        elements.push(k.1);
    }

    Ok((i, Section::Element(ElementSection { entries: elements })))
}

fn parse_data_section<'a, 'b>(
    i: &'a [u8],
    _size: u32,
    counter: &'b mut Counter,
) -> IResult<&'a [u8], Section> {
    debug!("parse_data_section");
    let (mut i, times) = take_leb_u32(i)?;
    //let (i, k) = count(take_data, times as usize)(i)?;

    let mut entries = Vec::with_capacity(times as usize);
    for _ in 0..times {
        let k = take_data(i, counter)?;
        i = k.0;
        entries.push(k.1);
    }

    Ok((i, Section::Data(DataSection { entries })))
}

fn parse_code_section<'a, 'b>(
    i: &'a [u8],
    _size: u32,
    counter: &'b mut Counter,
) -> IResult<&'a [u8], Section> {
    debug!("parse_code_section");

    let (mut i, times) = take_leb_u32(i)?;
    debug!("times {}", times);
    //let (i, codes) = count(take_code, times as usize)(i)?;

    let mut codes = Vec::with_capacity(times as usize);
    for _ in 0..times {
        let k = take_code(i, counter)?;
        i = k.0;
        codes.push(k.1);
    }

    Ok((i, Section::Code(CodeSection { entries: codes })))
}

fn take_code<'a, 'b>(i: &'a [u8], counter: &'b mut Counter) -> IResult<&'a [u8], FunctionBody> {
    debug!("parse_code");

    let (i, _size) = take_leb_u32(i)?;
    let (i, k) = take_func(i, counter)?;

    Ok((i, k))
}

fn take_func<'a, 'b>(i: &'a [u8], counter: &'b mut Counter) -> IResult<&'a [u8], FunctionBody> {
    debug!("take_func");

    let (i, times) = take_leb_u32(i)?;
    debug!("times {}", times);
    let (i, locals) = count(take_local, times as usize)(i)?;

    debug!("locals {:?}", locals);

    let (i, code) = take_expr(i, counter)?;

    Ok((
        i,
        FunctionBody {
            locals,
            code: InstructionWrapper::wrap_instructions(counter, code),
        },
    ))
}

fn take_local(i: &[u8]) -> IResult<&[u8], LocalEntry> {
    debug!("take_local");

    let (i, n) = take_leb_u32(i)?;
    debug!("local n {:?}", n);
    //debug!("local i {:?}", i);
    let (i, t) = take_valtype(i)?;

    Ok((i, LocalEntry { count: n, ty: t }))
}

fn take_data<'a, 'b>(i: &'a [u8], counter: &'b mut Counter) -> IResult<&'a [u8], DataSegment> {
    debug!("take_data");

    let (i, mem_idx) = take_leb_u32(i)?;
    let (i, e) = take_expr(i, counter)?;

    let (i, times) = take_leb_u32(i)?;
    let (i, b) = count(take(1u8), times as usize)(i)?;

    Ok((
        i,
        DataSegment {
            data: mem_idx,
            offset: InstructionWrapper::wrap_instructions(counter, e),
            init: b.into_iter().map(|w| w[0]).collect(),
        },
    ))
}

fn take_elem<'a, 'b>(i: &'a [u8], counter: &'b mut Counter) -> IResult<&'a [u8], ElementSegment> {
    debug!("take_elem");

    let (i, table_idx) = take_leb_u32(i)?;
    let (i, e) = take_expr(i, counter)?;
    let (i, times) = take_leb_u32(i)?;
    let (i, y_vec) = count(take_leb_u32, times as usize)(i)?;

    Ok((
        i,
        ElementSegment {
            table: table_idx,
            offset: InstructionWrapper::wrap_instructions(counter, e),
            init: y_vec,
        },
    ))
}

fn take_export(i: &[u8]) -> IResult<&[u8], ExportEntry> {
    debug!("take_export");

    let (i, name) = take_name(i)?;
    let (i, kind) = take_desc(i)?;

    Ok((i, ExportEntry { name, kind }))
}

fn take_global<'a, 'b>(i: &'a [u8], counter: &'b mut Counter) -> IResult<&'a [u8], GlobalVariable> {
    let (i, ty) = take_globaltype(i)?;
    let (i, e) = take_expr(i, counter)?;

    Ok((
        i,
        GlobalVariable {
            ty,
            init: InstructionWrapper::wrap_instructions(counter, e),
        },
    ))
}

pub(crate) fn take_expr<'a, 'b>(
    mut i: &'a [u8],
    counter: &'b mut Counter,
) -> IResult<&'a [u8], Vec<Instruction>> {
    debug!("take expr");

    let mut instructions = Vec::new();

    loop {
        let (_, k) = take(1u8)(i)?; //0x0B

        if k == END_INSTR {
            break;
        }

        let (w, ii) = instructions::parse_instr(i, counter)?;
        instructions.push(ii);
        i = w;
    }

    let (i, e) = take(1u8)(i)?; //0x0B
    assert_eq!(e, END_INSTR);

    Ok((i, instructions))
}

fn take_import(i: &[u8]) -> IResult<&[u8], ImportEntry> {
    debug!("take_import");

    let (i, module_name) = take_name(i)?;
    let (i, name) = take_name(i)?;
    let (i, desc) = take_import_desc(i)?;

    Ok((
        i,
        ImportEntry {
            module_name,
            name,
            desc,
        },
    ))
}

fn take_import_desc(i: &[u8]) -> IResult<&[u8], ImportDesc> {
    debug!("take_desc");

    let (i, b) = take(1u8)(i)?;

    let (i, desc) = match b[0] {
        0x00 => {
            let (i, t) = take_leb_u32(&i)?;
            (i, ImportDesc::Function { ty: t })
        }
        0x01 => {
            let (i, t) = take_tabletype(&i)?;
            (i, ImportDesc::Table { ty: t })
        }
        0x02 => {
            let (i, t) = take_memtype(&i)?;
            (i, ImportDesc::Memory { ty: t })
        }
        0x03 => {
            let (i, t) = take_globaltype(&i)?;
            (i, ImportDesc::Global { ty: t })
        }
        _ => panic!("desc failed"),
    };

    Ok((i, desc))
}

fn take_desc(i: &[u8]) -> IResult<&[u8], ExternalKindType> {
    debug!("take_desc");

    let (i, b) = take(1u8)(i)?;

    let (i, desc) = match b[0] {
        0x00 => {
            let (i, t) = take_leb_u32(&i)?;
            (i, ExternalKindType::Function { ty: t })
        }
        0x01 => {
            let (i, t) = take_leb_u32(&i)?;
            (i, ExternalKindType::Table { ty: t })
        }
        0x02 => {
            let (i, t) = take_leb_u32(&i)?;
            (i, ExternalKindType::Memory { ty: t })
        }
        0x03 => {
            let (i, t) = take_leb_u32(&i)?;
            (i, ExternalKindType::Global { ty: t })
        }
        _ => panic!("desc failed"),
    };

    Ok((i, desc))
}

fn take_memtype(i: &[u8]) -> IResult<&[u8], MemoryType> {
    debug!("take_memtype");
    let (i, l) = take_limits(i)?;

    Ok((i, MemoryType { limits: l }))
}

fn take_tabletype(i: &[u8]) -> IResult<&[u8], TableType> {
    debug!("take_tabletype");
    let (i, element_type) = take(1u8)(i)?;
    assert_eq!(0x70, element_type[0]);
    let (i, limits) = take_limits(i)?;

    Ok((
        i,
        TableType {
            element_type: 0x70,
            limits,
        },
    ))
}

fn take_globaltype(i: &[u8]) -> IResult<&[u8], GlobalType> {
    debug!("take_globaltype");
    let (i, val) = take_valtype(i)?;
    let (i, b) = take_byte(i, 1)?;

    let mu = match b[0] {
        0x00 => Mu::Const,
        0x01 => Mu::Var,
        _ => panic!("wrong mu"),
    };

    Ok((
        i,
        GlobalType {
            value_type: val,
            mu,
        },
    ))
}

fn take_limits(i: &[u8]) -> IResult<&[u8], Limits> {
    debug!("take_limits");
    let (i, n) = take(1u8)(i)?;

    Ok(match n[0] {
        0x00 => {
            let (i, n) = take_leb_u32(i)?;

            (i, Limits::Zero(n))
        }
        0x01 => {
            let (i, n) = take_leb_u32(i)?;
            let (i, m) = take_leb_u32(i)?;

            (i, Limits::One(n, m))
        }
        _ => panic!("Limit has wrong tag"),
    })
}

fn take_function_signature(i: &[u8]) -> IResult<&[u8], FunctionSignature> {
    debug!("take_function_signature");

    let (i, offset) = take(1u8)(i)?; //0x60

    assert_eq!(offset[0], 0x60);

    let (i, times) = take_leb_u32(i)?;
    let (i, t1) = count(take(1u8), times as usize)(i)?;
    let (i, times) = take_leb_u32(i)?;
    let (i, t2) = count(take(1u8), times as usize)(i)?;

    let param_types: Vec<_> = t1.into_iter().map(|w| w[0].into()).collect();
    let return_types: Vec<_> = t2.into_iter().map(|w| w[0].into()).collect();

    Ok((
        i,
        FunctionSignature {
            param_types,
            return_types,
        },
    ))
}

fn take_valtype(i: &[u8]) -> IResult<&[u8], ValueType> {
    debug!("take_valtype");
    let (i, n) = take(1u8)(i)?;

    Ok((i, n[0].into()))
}

fn take_blocktype(i: &[u8]) -> IResult<&[u8], BlockType> {
    debug!("take_blocktype");
    let (u, n) = take(1u8)(i)?;
    debug!("n {:?}", n);

    let (i, bty) = match n[0] {
        0x40 => (u, BlockType::Empty),
        0x7F | 0x7E | 0x7D | 0x7C => (u, BlockType::ValueType(n[0].into())),
        _ => {
            // This must be signed 33 bit
            // Weird, Page 96 spec
            let (i, k) = take_leb_i33(i)?;

            (i, BlockType::FuncTy(k as u32))
        }
    };

    Ok((i, bty))
}

fn take_byte(i: &[u8], len: u32) -> IResult<&[u8], &[u8]> {
    debug!("take_byte");
    take(len as usize)(i)
}

pub(crate) fn take_f32(i: &[u8]) -> IResult<&[u8], f32> {
    debug!("take_f32");
    let (i, bytes) = take(4u8)(i)?;

    Ok((i, LittleEndian::read_f32(bytes)))
}

pub(crate) fn take_f64(i: &[u8]) -> IResult<&[u8], f64> {
    debug!("take_f64");
    let (i, bytes) = take(8u8)(i)?;

    Ok((i, LittleEndian::read_f64(bytes)))
}

fn take_name(i: &[u8]) -> IResult<&[u8], String> {
    debug!("take_name");
    let (i, times) = take_leb_u32(i)?;
    let (i, vec) = count(take(1u8), times as usize)(i)?;

    let vec2: Vec<_> = vec.into_iter().map(|w| w[0]).collect();

    Ok((i, String::from_utf8(vec2).unwrap()))
}

pub(crate) fn take_leb_u32(i: &[u8]) -> IResult<&[u8], u32> {
    debug!("take_leb_u32");
    if i.len() >= 5 {
        let (_, bytes) = take(5u8)(i)?;
        let leb = read_u32_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    } else {
        let (_, bytes) = take(i.len())(i)?;
        let leb = read_u32_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    }
}

pub(crate) fn take_leb_i32(i: &[u8]) -> IResult<&[u8], i32> {
    debug!("take_leb_i32");
    if i.len() >= 5 {
        let (_, bytes) = take(5u8)(i)?;
        let leb = read_i32_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    } else {
        let (_, bytes) = take(i.len())(i)?;
        let leb = read_i32_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    }
}

pub(crate) fn take_leb_i64(i: &[u8]) -> IResult<&[u8], i64> {
    debug!("take_leb_i64");
    if i.len() >= 10 {
        let (_, bytes) = take(10u8)(i)?;
        let leb = read_i64_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    } else {
        let (_, bytes) = take(i.len())(i)?;
        let leb = read_i64_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    }
}

pub(crate) fn take_leb_i33(i: &[u8]) -> IResult<&[u8], i64> {
    debug!("take_leb_i33");
    if i.len() >= 6 {
        let (_, bytes) = take(6u8)(i)?;
        let leb = read_i33_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    } else {
        let (_, bytes) = take(i.len())(i)?;
        let leb = read_i33_leb128(bytes);
        let (i, _) = take(leb.1)(i)?; //skip the bytes, which contain leb

        Ok((i, leb.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;

    macro_rules! test_file {
        ($fs_name:expr) => {
            let file = read_wasm!(&format!("test_files/{}", $fs_name));
            let ast = parse(file).unwrap();
            assert_snapshot!($fs_name, format!("{:#?}", ast));
        };
    }

    #[test]
    fn test_take_leb_i32() {
        let bytes = [0x7f, 0, 0, 0];

        let (_, n) = take_leb_i32(&bytes).unwrap();

        assert_eq!(n, -1);
    }

    #[test]
    fn test_take_leb_i33() {
        let bytes = [0x7f, 0, 0, 0];

        let (_, n) = take_leb_i33(&bytes).unwrap();

        assert_eq!(n, -1);
    }

    #[test]
    fn test_take_leb_i64() {
        let bytes = [0x7f, 0, 0, 0];

        let (_, n) = take_leb_i64(&bytes).unwrap();

        assert_eq!(n, -1);
    }

    #[test]
    fn test_take_leb_i64_2() {
        let bytes = [0x3c, 0, 0, 0];

        let (_, n) = take_leb_i64(&bytes).unwrap();

        assert_eq!(n, 0x3c);
    }

    #[test]
    fn test_take_leb_i64_3() {
        let bytes = [0x80, 0x7f];

        let (_, n) = take_leb_i64(&bytes).unwrap();

        assert_eq!(n, -128);
    }

    #[test]
    fn test_take_leb_u32_n135() {
        let bytes = [135u8, 0x01];

        let (_, n) = take_leb_u32(&bytes).unwrap();

        assert_eq!(n, 135);
    }

    #[test]
    fn test_take_leb_i32_n8192() {
        let bytes = [0x80, 0xc0, 0x00];

        let (_, n) = take_leb_i32(&bytes).unwrap();

        assert_eq!(n, 8192);
    }

    #[test]
    fn test_take_leb_i32_neg_n8192() {
        let bytes = [0x80, 0x40];

        let (_, n) = take_leb_i32(&bytes).unwrap();

        assert_eq!(n, -8192);
    }

    #[test]
    fn test_take_leb_i64_n8192() {
        let bytes = [0x80, 0xc0, 0x00];

        let (_, n) = take_leb_i64(&bytes).unwrap();

        assert_eq!(n, 8192);
    }

    #[test]
    fn test_take_leb_i64_neg_n8192() {
        let bytes = [0x80, 0x40];

        let (_, n) = take_leb_i64(&bytes).unwrap();

        assert_eq!(n, -8192);
    }

    #[test]
    fn test_take_leb_i64_min() {
        let bytes = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f];

        let (_, n) = take_leb_i64(&bytes).unwrap();

        assert_eq!(n, -9223372036854775808);
    }

    #[test]
    fn test_empty_wasm() {
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
