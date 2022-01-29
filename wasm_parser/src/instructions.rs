use anyhow::Result;
use log::debug;

use crate::core::*;
use crate::{
    consume_byte, take_blocktype, take_f32, take_f64, take_leb_i32, take_leb_i64, take_leb_u32,
    BytesReader,
};

const END_INSTR: &[u8] = &[0x0B];
const END_IF_BLOCK: &[u8] = &[0x05];

pub(crate) fn parse_instr<'b>(
    i: &mut BytesReader,
    counter: &'b mut Counter,
) -> Result<Instruction> {
    debug!("parse_instr");
    debug!("---------------");
    let instr = consume_byte!(i);
    debug!("HEAD {:x?}", instr);

    let expr = match instr[0] {
        0x00 => (Instruction::OP_UNREACHABLE),
        0x01 => (Instruction::OP_NOP),
        0x02 => take_block(i, counter)?,
        0x03 => take_loop(i, counter)?,
        0x04 => take_conditional(i, counter)?,
        0x0C => take_br(i)?,
        0x0D => take_br_if(i)?,
        0x0E => take_br_table(i)?,
        0x0F => (Instruction::OP_RETURN),
        0x10 => take_call(i)?,
        0x11 => take_call_indirect(i)?,
        // Parametric
        0x1A => (Instruction::OP_DROP),
        0x1B => (Instruction::OP_SELECT),
        // Var
        0x20 => {
            let idx = crate::take_leb_u32(i)?;
            let block = Instruction::OP_LOCAL_GET(idx);
            block
        }
        0x21 => {
            let idx = crate::take_leb_u32(i)?;
            let block = Instruction::OP_LOCAL_SET(idx);
            block
        }
        0x22 => {
            let idx = crate::take_leb_u32(i)?;
            let block = Instruction::OP_LOCAL_TEE(idx);
            block
        }
        0x23 => {
            let idx = crate::take_leb_u32(i)?;
            let block = Instruction::OP_GLOBAL_GET(idx);
            block
        }
        0x24 => {
            let idx = crate::take_leb_u32(i)?;
            let block = Instruction::OP_GLOBAL_SET(idx);
            block
        }
        // Memory
        0x28 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_LOAD(m);
            block
        }
        0x29 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD(m);
            block
        }
        0x2A => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_F32_LOAD(m);
            block
        }
        0x2B => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_F64_LOAD(m);
            block
        }
        0x2C => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_LOAD_8_s(m);
            block
        }
        0x2D => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_LOAD_8_u(m);
            block
        }
        0x2E => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_LOAD_16_s(m);
            block
        }
        0x2F => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_LOAD_16_u(m);
            block
        }
        0x30 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD_8_s(m);
            block
        }
        0x31 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD_8_u(m);
            block
        }
        0x32 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD_16_s(m);
            block
        }
        0x33 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD_16_u(m);
            block
        }
        0x34 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD_32_s(m);
            block
        }
        0x35 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_LOAD_32_u(m);
            block
        }
        0x36 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_STORE(m);
            block
        }
        0x37 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_STORE(m);
            block
        }
        0x38 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_F32_STORE(m);
            block
        }
        0x39 => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_F64_STORE(m);
            block
        }
        0x3a => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_STORE_8(m);
            block
        }
        0x3b => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I32_STORE_16(m);
            block
        }
        0x3c => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_STORE_8(m);
            block
        }
        0x3d => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_STORE_16(m);
            block
        }
        0x3e => {
            let m = take_memarg(i)?;
            let block = Instruction::OP_I64_STORE_32(m);
            block
        }
        0x3f => {
            let m = consume_byte!(i);
            assert_eq!([0x00], m);
            let block = Instruction::OP_MEMORY_SIZE;
            block
        }
        0x40 => {
            let m = consume_byte!(i);
            assert_eq!([0x00], m);
            let block = Instruction::OP_MEMORY_GROW;
            block
        }
        // Numeric Instructions
        0x41 => {
            let m = take_leb_i32(i)?;
            let block = Instruction::OP_I32_CONST(m);
            block
        }
        0x42 => {
            let m = take_leb_i64(i)?;
            let block = Instruction::OP_I64_CONST(m);
            block
        }
        0x43 => {
            let m = take_f32(i)?;
            let block = Instruction::OP_F32_CONST(m);
            block
        }
        0x44 => {
            let m = take_f64(i)?;
            let block = Instruction::OP_F64_CONST(m);
            block
        }
        0x45 => (Instruction::OP_I32_EQ),
        0x47 => (Instruction::OP_I32_NE),
        0x48 => (Instruction::OP_I32_LT_S),
        0x49 => (Instruction::OP_I32_LT_U),
        0x4a => (Instruction::OP_I32_GT_S),
        0x4b => (Instruction::OP_I32_GT_U),
        0x4c => (Instruction::OP_I32_LE_S),
        0x4d => (Instruction::OP_I32_LE_U),
        0x4e => (Instruction::OP_I32_GE_S),
        0x4f => (Instruction::OP_I32_GE_U),
        0x50 => (Instruction::OP_I64_EQZ),
        0x51 => (Instruction::OP_I64_EQ),
        0x52 => (Instruction::OP_I64_NE),
        0x53 => (Instruction::OP_I64_LT_S),
        0x54 => (Instruction::OP_I64_LT_U),
        0x55 => (Instruction::OP_I64_GT_S),
        0x56 => (Instruction::OP_I64_GT_U),
        0x57 => (Instruction::OP_I64_LE_S),
        0x58 => (Instruction::OP_I64_LE_U),
        0x59 => (Instruction::OP_I64_GE_S),
        0x5a => (Instruction::OP_I64_GE_U),

        0x5b => (Instruction::OP_F32_EQ),
        0x5c => (Instruction::OP_F32_NE),
        0x5d => (Instruction::OP_F32_LT),
        0x5e => (Instruction::OP_F32_GT),
        0x5f => (Instruction::OP_F32_LE),
        0x60 => (Instruction::OP_F32_GE),

        0x61 => (Instruction::OP_F64_EQ),
        0x62 => (Instruction::OP_F64_NE),
        0x63 => (Instruction::OP_F64_LT),
        0x64 => (Instruction::OP_F64_GT),
        0x65 => (Instruction::OP_F64_LE),
        0x66 => (Instruction::OP_F64_GE),

        0x67 => (Instruction::OP_I32_CLZ),
        0x68 => (Instruction::OP_I32_CTZ),
        0x69 => (Instruction::OP_I32_POPCNT),
        0x6a => (Instruction::OP_I32_ADD),
        0x6b => (Instruction::OP_I32_SUB),
        0x6c => (Instruction::OP_I32_MUL),
        0x6d => (Instruction::OP_I32_DIV_S),
        0x6e => (Instruction::OP_I32_DIV_U),
        0x6f => (Instruction::OP_I32_REM_S),
        0x70 => (Instruction::OP_I32_REM_U),
        0x71 => (Instruction::OP_I32_AND),
        0x72 => (Instruction::OP_I32_OR),
        0x73 => (Instruction::OP_I32_XOR),
        0x74 => (Instruction::OP_I32_SHL),
        0x75 => (Instruction::OP_I32_SHR_S),
        0x76 => (Instruction::OP_I32_SHR_U),
        0x77 => (Instruction::OP_I32_ROTL),
        0x78 => (Instruction::OP_I32_ROTR),

        0x79 => (Instruction::OP_I64_CLZ),
        0x7a => (Instruction::OP_I64_CTZ),
        0x7b => (Instruction::OP_I64_POPCNT),
        0x7c => (Instruction::OP_I64_ADD),
        0x7d => (Instruction::OP_I64_SUB),
        0x7e => (Instruction::OP_I64_MUL),
        0x7f => (Instruction::OP_I64_DIV_S),
        0x80 => (Instruction::OP_I64_DIV_U),
        0x81 => (Instruction::OP_I64_REM_S),
        0x82 => (Instruction::OP_I64_REM_U),
        0x83 => (Instruction::OP_I64_AND),
        0x84 => (Instruction::OP_I64_OR),
        0x85 => (Instruction::OP_I64_XOR),
        0x86 => (Instruction::OP_I64_SHL),
        0x87 => (Instruction::OP_I64_SHR_S),
        0x88 => (Instruction::OP_I64_SHR_U),
        0x89 => (Instruction::OP_I64_ROTL),
        0x8a => (Instruction::OP_I64_ROTR),

        0x8b => (Instruction::OP_F32_ABS),
        0x8c => (Instruction::OP_F32_NEG),
        0x8d => (Instruction::OP_F32_CEIL),
        0x8e => (Instruction::OP_F32_FLOOR),
        0x8f => (Instruction::OP_F32_TRUNC),
        0x90 => (Instruction::OP_F32_NEAREST),
        0x91 => (Instruction::OP_F32_SQRT),
        0x92 => (Instruction::OP_F32_ADD),
        0x93 => (Instruction::OP_F32_SUB),
        0x94 => (Instruction::OP_F32_MUL),
        0x95 => (Instruction::OP_F32_DIV),
        0x96 => (Instruction::OP_F32_MIN),
        0x97 => (Instruction::OP_F32_MAX),
        0x98 => (Instruction::OP_F32_COPYSIGN),

        0x99 => (Instruction::OP_F64_ABS),
        0x9a => (Instruction::OP_F64_NEG),
        0x9b => (Instruction::OP_F64_CEIL),
        0x9c => (Instruction::OP_F64_FLOOR),
        0x9d => (Instruction::OP_F64_TRUNC),
        0x9e => (Instruction::OP_F64_NEAREST),
        0x9f => (Instruction::OP_F64_SQRT),
        0xa0 => (Instruction::OP_F64_ADD),
        0xa1 => (Instruction::OP_F64_SUB),
        0xa2 => (Instruction::OP_F64_MUL),
        0xa3 => (Instruction::OP_F64_DIV),
        0xa4 => (Instruction::OP_F64_MIN),
        0xa5 => (Instruction::OP_F64_MAX),
        0xa6 => (Instruction::OP_F64_COPYSIGN),

        0xa7 => (Instruction::OP_I32_WRAP_I64),
        0xa8 => (Instruction::OP_I32_TRUNC_F32_S),
        0xa9 => (Instruction::OP_I32_TRUNC_F32_U),
        0xaa => (Instruction::OP_I32_TRUNC_F64_S),
        0xab => (Instruction::OP_I32_TRUNC_F64_U),
        0xac => (Instruction::OP_I64_EXTEND_I32_S),
        0xad => (Instruction::OP_I64_EXTEND_I32_U),
        0xae => (Instruction::OP_I64_TRUNC_F32_S),
        0xaf => (Instruction::OP_I64_TRUNC_F32_U),
        0xb0 => (Instruction::OP_I64_TRUNC_F64_S),
        0xb1 => (Instruction::OP_I64_TRUNC_F64_U),
        0xb2 => (Instruction::OP_F32_CONVERT_I32_S),
        0xb3 => (Instruction::OP_F32_CONVERT_I32_U),
        0xb4 => (Instruction::OP_F32_CONVERT_I64_S),
        0xb5 => (Instruction::OP_F32_CONVERT_I64_U),
        0xb6 => (Instruction::OP_F32_DEMOTE_F64),
        0xb7 => (Instruction::OP_F64_CONVERT_I32_S),
        0xb8 => (Instruction::OP_F64_CONVERT_I32_U),
        0xb9 => (Instruction::OP_F64_CONVERT_I64_S),
        0xba => (Instruction::OP_F64_CONVERT_I64_U),
        0xbb => (Instruction::OP_F64_PROMOTE_F32),
        0xbc => (Instruction::OP_I32_REINTERPRET_F32),
        0xbd => (Instruction::OP_I64_REINTERPRET_F64),
        0xbe => (Instruction::OP_F32_REINTERPRET_I32),
        0xbf => (Instruction::OP_F64_REINTERPRET_I64),
        0xc0 => (Instruction::OP_I32_EXTEND8_S),
        0xc1 => (Instruction::OP_I32_EXTEND16_S),
        0xc2 => (Instruction::OP_I64_EXTEND8_S),
        0xc3 => (Instruction::OP_I64_EXTEND16_S),
        0xc4 => (Instruction::OP_I64_EXTEND32_S),

        0xfc => {
            let m = consume_byte!(i);
            match m {
                [0x00] => Instruction::OP_I32_TRUNC_SAT_F32_S,
                [0x01] => Instruction::OP_I32_TRUNC_SAT_F32_U,
                [0x02] => Instruction::OP_I32_TRUNC_SAT_F64_S,
                [0x03] => Instruction::OP_I32_TRUNC_SAT_F64_U,

                [0x04] => Instruction::OP_I64_TRUNC_SAT_F32_S,
                [0x05] => Instruction::OP_I64_TRUNC_SAT_F32_U,
                [0x06] => Instruction::OP_I64_TRUNC_SAT_F64_S,
                [0x07] => Instruction::OP_I64_TRUNC_SAT_F64_U,
                _ => anyhow::bail!("Invalid saturating instruction"),
            }
        }
        _ => anyhow::bail!("unknown instruction {}", instr[0]),
    };

    Ok(expr)
}

fn take_block<'a, 'b>(i: &mut BytesReader, counter: &'a mut Counter) -> Result<Instruction> {
    let block_ty = take_blocktype(i)?;

    let mut instructions = Vec::new();

    loop {
        let k = consume_byte!(i); //0x0B

        if k == END_INSTR {
            break;
        }

        let instruction = parse_instr(i, counter)?;
        instructions.push(instruction);
    }

    let e = consume_byte!(i); //0x0B
    assert_eq!(e, END_INSTR);

    let block = Instruction::OP_BLOCK(block_ty, CodeBlock::new(counter, instructions));

    Ok(block)
}

fn take_loop<'a, 'b>(i: &mut BytesReader, counter: &'a mut Counter) -> Result<Instruction> {
    let block_ty = take_blocktype(i)?;

    let mut instructions = Vec::new();

    loop {
        let k = consume_byte!(i); //0x0B

        if k == END_INSTR {
            break;
        }

        let instruction = parse_instr(i, counter)?;
        instructions.push(instruction);
    }

    let e = consume_byte!(i); //0x0B
    assert_eq!(e, END_INSTR);

    let block = Instruction::OP_LOOP(block_ty, CodeBlock::new(counter, instructions));

    Ok(block)
}

fn take_conditional<'a, 'b>(i: &mut BytesReader, counter: &'a mut Counter) -> Result<Instruction> {
    debug!("take_conditional");

    let block_ty = take_blocktype(i)?;

    let mut instructions = Vec::new();
    let mut else_instructions = Vec::new();

    loop {
        let k = consume_byte!(i); //0x0B or 0x05

        if k == END_IF_BLOCK || k == END_INSTR {
            break;
        }

        let instruction = parse_instr(i, counter)?;
        instructions.push(instruction);
    }

    let k = consume_byte!(i); //0x0B or 0x05

    if k == END_IF_BLOCK {
        //THIS IS THE ELSE BLOCK
        loop {
            let k = consume_byte!(i); //0x0B

            if k == END_INSTR {
                break;
            }

            let instruction = parse_instr(i, counter)?;
            else_instructions.push(instruction);
        }

        let e = consume_byte!(i);
        assert_eq!(END_INSTR, e);

        return Ok(Instruction::OP_IF_AND_ELSE(
            block_ty,
            CodeBlock::new(counter, instructions),
            CodeBlock::new(counter, else_instructions),
        ));
    }

    Ok(Instruction::OP_IF(
        block_ty,
        CodeBlock::new(counter, instructions),
    ))
}

fn take_br(i: &mut BytesReader) -> Result<Instruction> {
    let labelidx = crate::take_leb_u32(i)?;

    let block = Instruction::OP_BR(labelidx);

    Ok(block)
}

fn take_br_if(i: &mut BytesReader) -> Result<Instruction> {
    let labelidx = crate::take_leb_u32(i)?;

    let block = Instruction::OP_BR_IF(labelidx);

    Ok(block)
}

fn take_br_table(i: &mut BytesReader) -> Result<Instruction> {
    let n = crate::take_leb_u32(i)?;
    let mut ids = Vec::with_capacity(n as usize);

    for _ in 0..n {
        let id = take_leb_u32(i)?;
        ids.push(id);
    }

    let l_n = crate::take_leb_u32(i)?;

    let block = Instruction::OP_BR_TABLE(ids, l_n);

    Ok(block)
}

fn take_call(i: &mut BytesReader) -> Result<Instruction> {
    let func_idx = crate::take_leb_u32(i)?;

    let block = Instruction::OP_CALL(func_idx);

    Ok(block)
}

fn take_call_indirect(i: &mut BytesReader) -> Result<Instruction> {
    let type_idx = crate::take_leb_u32(i)?;
    let b = consume_byte!(i);

    assert_eq!(b, [0x00]);

    let block = Instruction::OP_CALL_INDIRECT(type_idx);

    Ok(block)
}

fn take_memarg(i: &mut BytesReader) -> Result<MemArg> {
    let n = crate::take_leb_u32(i)?;
    let o = crate::take_leb_u32(i)?;

    Ok(MemArg {
        align: n,
        offset: o,
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::{BufReader, Read};

    #[test]
    fn test_instruction_block() {
        //env_logger::init();

        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_block(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        assert_eq!(
            instructions,
            Instruction::OP_BLOCK(
                BlockType::Empty,
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP, Instruction::OP_NOP])
            )
        );
    }

    #[test]
    fn test_instruction_block_val_type() {
        //env_logger::init();

        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x7C); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_block(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        assert_eq!(
            instructions,
            Instruction::OP_BLOCK(
                BlockType::ValueType(ValueType::F64),
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP, Instruction::OP_NOP])
            )
        );
    }

    #[test]
    fn test_instruction_block_s33() {
        //env_logger::init();

        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x80); // s33
        payload.push(0x7f); // s33
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_block(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        assert_eq!(
            instructions,
            Instruction::OP_BLOCK(
                BlockType::FuncTy(-128),
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP, Instruction::OP_NOP])
            )
        );
    }

    #[test]
    fn test_instruction_block_nested_2() {
        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x0B); //end
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_block(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        let innerblock = CodeBlock::new(&mut counter, vec![Instruction::OP_NOP]);

        assert_eq!(
            instructions,
            Instruction::OP_BLOCK(
                BlockType::Empty,
                CodeBlock::new(
                    &mut counter,
                    vec![
                        Instruction::OP_NOP,
                        Instruction::OP_NOP,
                        Instruction::OP_BLOCK(BlockType::Empty, innerblock),
                        Instruction::OP_NOP,
                    ]
                )
            )
        );
    }

    #[test]
    fn test_instruction_block_nested_3() {
        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x0B); //end
        payload.push(0x0B); //end
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_block(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        let block1 = CodeBlock::new(&mut counter, vec![]);

        let block3 = CodeBlock::new(
            &mut counter,
            vec![Instruction::OP_BLOCK(BlockType::Empty, block1)],
        );

        let block2 = CodeBlock::new(
            &mut counter,
            vec![Instruction::OP_BLOCK(BlockType::Empty, block3)],
        );

        assert_eq!(
            instructions,
            Instruction::OP_BLOCK(BlockType::Empty, block2)
        );
    }

    #[test]
    fn test_instruction_if() {
        //env_logger::init();

        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();

        let mut reader = BufReader::new(payload.as_slice());
        let instructions = take_conditional(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        assert_eq!(
            instructions,
            Instruction::OP_IF(
                BlockType::Empty,
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP, Instruction::OP_NOP])
            )
        );
    }

    #[test]
    fn test_instruction_if_conditionals() {
        //env_logger::init();

        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x05); //else
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_conditional(&mut reader, &mut counter).unwrap();

        //debug!("{:?}", instructions);
        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        assert_eq!(
            instructions,
            Instruction::OP_IF_AND_ELSE(
                BlockType::Empty,
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP]),
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP])
            )
        );
    }

    #[test]
    fn test_instruction_loop() {
        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x0B); //end

        let mut counter = Counter::default();
        let mut reader = BufReader::new(payload.as_slice());

        let instructions = take_loop(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        assert_eq!(
            instructions,
            Instruction::OP_LOOP(
                BlockType::Empty,
                CodeBlock::new(&mut counter, vec![Instruction::OP_NOP, Instruction::OP_NOP]),
            )
        );
    }

    #[test]
    fn test_instruction_loop_nested() {
        let mut payload = Vec::new();
        //payload.push(0x02); // block
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x03); // empty
        payload.push(0x40); // empty
        payload.push(0x01); //nop
        payload.push(0x01); //nop
        payload.push(0x0B); //end
        payload.push(0x0B); //end

        let mut counter = Counter::default();

        let mut reader = BufReader::new(payload.as_slice());
        let instructions = take_loop(&mut reader, &mut counter).unwrap();

        let mut buff = [0u8; 1];
        let _ = reader.read_exact(&mut buff);
        assert_ne!(buff, [11]);

        let mut counter = Counter::default();

        let innerblock =
            CodeBlock::new(&mut counter, vec![Instruction::OP_NOP, Instruction::OP_NOP]);

        assert_eq!(
            instructions,
            Instruction::OP_LOOP(
                BlockType::Empty,
                CodeBlock::new(
                    &mut counter,
                    vec![
                        Instruction::OP_NOP,
                        Instruction::OP_NOP,
                        Instruction::OP_LOOP(BlockType::Empty, innerblock)
                    ]
                ),
            )
        );
    }
}
