use crate::engine::StackContent::*;
use crate::engine::Value::*;
use anyhow::{anyhow, Context, Result};
use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};
use wasm_parser::core::CtrlInstructions::*;
use wasm_parser::core::Instruction::*;
use wasm_parser::core::MemoryInstructions::*;
use wasm_parser::core::NumericInstructions::*;
use wasm_parser::core::ParamInstructions::*;
use wasm_parser::core::VarInstructions::*;
use wasm_parser::core::*;
use wasm_parser::Module;

pub(crate) const PAGE_SIZE: usize = 65536;

#[derive(Debug)]
pub struct Engine {
    pub module: ModuleInstance, //TODO rename to `module_instance`
    pub started: bool,
    pub store: Store,
}

#[derive(Debug)]
pub enum InstructionOutcome {
    EXIT,
    BRANCH(u32),
    RETURN,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Value {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
}

type Arity = u32;

impl Into<ValueType> for Value {
    fn into(self) -> ValueType {
        match self {
            Value::I32(_) => ValueType::I32,
            Value::I64(_) => ValueType::I64,
            Value::F32(_) => ValueType::F32,
            Value::F64(_) => ValueType::F64,
        }
    }
}

impl Value {
    fn convert(self, vt: ValueType) -> Value {
        trace!("Convert {:?} to {:?}", self, vt);
        match (self, vt) {
            (Value::I32(v), ValueType::I64) => Value::I64(v as i64),
            (Value::I32(v), ValueType::F32) => Value::F32(v as f32),
            (Value::I32(v), ValueType::F64) => Value::F64(v as f64),
            (Value::I64(v), ValueType::I32) => Value::I32(v as i32),
            (Value::I64(v), ValueType::F32) => Value::F32(v as f32),
            (Value::I64(v), ValueType::F64) => Value::F64(v as f64),
            (Value::F32(v), ValueType::F64) => Value::F64(v as f64),
            (Value::F32(v), ValueType::I32) => Value::I32(v as i32),
            (Value::F32(v), ValueType::I64) => Value::I64(v as i64),
            (Value::F64(v), ValueType::F32) => Value::F32(v as f32),
            (Value::F64(v), ValueType::I32) => Value::I32(v as i32),
            (Value::F64(v), ValueType::I64) => Value::I64(v as i64),
            _ => self,
        }
    }

    pub fn signum(&self) -> f32 {
        match self {
            Value::F32(k) => k.signum() as f32,
            Value::F64(k) => k.signum() as f32,
            Value::I32(k) => k.signum() as f32,
            Value::I64(k) => k.signum() as f32,
        }
    }

    pub fn is_f32(&self) -> bool {
        match self {
            Value::F32(_) => true,
            _ => false,
        }
    }

    pub fn is_f64(&self) -> bool {
        match self {
            Value::F64(_) => true,
            _ => false,
        }
    }
}

impl Add for Value {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_add(v2)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_add(v2)),
            (F32(v1), F32(v2)) => F32(v1 + v2),
            (F64(v1), F64(v2)) => F64(v1 + v2),
            _ => panic!("Type missmatch during addition"),
        }
    }
}

impl Sub for Value {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_sub(v2)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_sub(v2)),
            (F32(v1), F32(v2)) => F32(v1 - v2),
            (F64(v1), F64(v2)) => F64(v1 - v2),
            _ => panic!("Type missmatch during subtraction"),
        }
    }
}

impl Mul for Value {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_mul(v2)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_mul(v2)),
            (F32(v1), F32(v2)) => F32(v1 * v2),
            (F64(v1), F64(v2)) => F64(v1 * v2),
            _ => panic!("Type missmatch during subtraction"),
        }
    }
}

impl Div for Value {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_div(v2)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_div(v2)),
            (F32(v1), F32(v2)) => F32(v1 / v2),
            (F64(v1), F64(v2)) => F64(v1 / v2),
            _ => panic!("Type missmatch during division"),
        }
    }
}

impl BitAnd for Value {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1 & v2),
            (I64(v1), I64(v2)) => I64(v1 & v2),
            _ => panic!("Type missmatch during bitand"),
        }
    }
}

impl BitOr for Value {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1 | v2),
            (I64(v1), I64(v2)) => I64(v1 | v2),
            _ => panic!("Type missmatch during bitor"),
        }
    }
}

impl BitXor for Value {
    type Output = Self;
    fn bitxor(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1 ^ v2),
            (I64(v1), I64(v2)) => I64(v1 ^ v2),
            _ => panic!("Type missmatch during bitxor"),
        }
    }
}

impl Shl for Value {
    type Output = Self;
    fn shl(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_shl(v2 as u32)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_shl(v2 as u32)),
            _ => panic!("Type missmatch during shift left"),
        }
    }
}

impl Shr for Value {
    type Output = Self;
    fn shr(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_shr(v2 as u32)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_shr(v2 as u32)),
            _ => panic!("Type missmatch during shift right"),
        }
    }
}

impl Rem for Value {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        match (self, other) {
            (I32(v1), I32(v2)) => I32(v1.wrapping_rem(v2)),
            (I64(v1), I64(v2)) => I64(v1.wrapping_rem(v2)),
            (F32(v1), F32(v2)) => F32(v1 % v2),
            (F64(v1), F64(v2)) => F64(v1 % v2),
            _ => panic!("Type missmatch during remainder"),
        }
    }
}

macro_rules! impl_two_op_integer {
    ($f:ident) => {
        fn $f(left: Value, right: Value) -> Value {
            match (left, right) {
                (I32(v1), I32(v2)) => I32(v1.$f(v2 as u32)),
                (I64(v1), I64(v2)) => I64(v1.$f(v2 as u32)),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
}

macro_rules! impl_two_op_all_numbers {
    ($f:ident, $k:expr) => {
        fn $f(left: Value, right: Value) -> Value {
            match (left, right) {
                (I32(v1), I32(v2)) => I32($k(v1, v2) as i32),
                (I64(v1), I64(v2)) => I64($k(v1, v2) as i64),
                (F32(v1), F32(v2)) => F32($k(v1, v2) as u32 as f32),
                (F64(v1), F64(v2)) => F64($k(v1, v2) as u32 as f64),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
}

macro_rules! impl_one_op_integer {
    ($f:ident) => {
        fn $f(left: Value) -> Value {
            match left {
                I32(v1) => I32(v1.$f() as i32),
                I64(v1) => I64(v1.$f() as i64),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
}

macro_rules! impl_one_op_float {
    ($f:ident) => {
        fn $f(left: Value) -> Value {
            match left {
                F32(v1) => F32(v1.$f() as f32),
                F64(v1) => F64(v1.$f() as f64),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
}

macro_rules! impl_one_op_float_closure {
    ($k:ident, $f:expr) => {
        fn $k(left: Value) -> Value {
            match left {
                F32(v1) => F32($f(v1.into()) as f32),
                F64(v1) => F64($f(v1) as f64),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
}

macro_rules! impl_two_op_float {
    ($f:ident, @nan $k:expr) => {
        fn $f(left: Value, right: Value) -> Value {
            match (left, right) {
                (F32(v1), F32(v2)) if v1.is_nan() || v2.is_nan() => F32(f32::NAN),
                (F64(v1), F64(v2)) if v1.is_nan() || v2.is_nan() => F64(f64::NAN),
                (F32(v1), F32(v2)) => F32($k(v1.into(), v2.into()) as f32),
                (F64(v1), F64(v2)) => F64($k(v1, v2) as f64),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
    ($f:ident, $k:expr) => {
        fn $f(left: Value, right: Value) -> Value {
            match (left, right) {
                (F32(v1), F32(v2)) => F32($k(v1.into(), v2.into()) as f32),
                (F64(v1), F64(v2)) => F64($k(v1, v2) as f64),
                _ => panic!("Type mismatch during {}", stringify!($f)),
            }
        }
    };
}

macro_rules! impl_trunc_sat_u {
    (@from $from_ty:ident @to $target:ident @but $cast:ident, $ret:ident, $fn:ident) => {
        pub(crate) fn $fn(f: Value) -> Value {
            let val = match f {
                $from_ty(v) => v,
                _ => panic!("Truncation only works on floats"),
            };

            if val.is_nan() {
                return $ret(0);
            }

            if val.is_infinite() {
                if val.is_sign_negative() {
                    return $ret(0);
                } else {
                    return $ret($target::MAX as $cast);
                }
            }

            return $ret(val.trunc() as $target as $cast);
        }
    };
}

macro_rules! impl_trunc_sat_s {
    (@from $bits:ident @to $target:ident, $ret:ident, $fn:ident) => {
        pub(crate) fn $fn(f: Value) -> Value {
            let val = match f {
                F32(v) => v as f64,
                F64(v) => v,
                _ => panic!("Truncation only works on floats"),
            };
            if val.is_nan() {
                return $ret(0);
            }

            if val.is_infinite() {
                if val.is_sign_negative() {
                    return $ret($bits::MIN as $target);
                } else {
                    return $ret($bits::MAX as $target);
                }
            }

            if val < $bits::MIN as f64 {
                return $ret($bits::MIN as $target);
            }
            if val > $bits::MAX as f64 {
                return $ret($bits::MAX as $target);
            }
            return $ret(val.trunc() as $target);
        }
    };
}

impl_two_op_integer!(rotate_left);
impl_two_op_integer!(rotate_right);

impl_one_op_integer!(leading_zeros);
impl_one_op_integer!(trailing_zeros);
impl_one_op_integer!(count_ones);

impl_two_op_all_numbers!(lt, |left, right| left < right);
impl_two_op_all_numbers!(gt, |left, right| left > right);
impl_two_op_all_numbers!(le, |left, right| left <= right);
impl_two_op_all_numbers!(ge, |left, right| left >= right);

impl_one_op_float!(abs);
impl_one_op_float_closure!(neg, |w: f64| -w);
impl_one_op_float!(ceil);
impl_one_op_float!(floor);
//impl_one_op_float!(round);
//impl_one_op_float!(nearest);
impl_one_op_float!(sqrt);
impl_one_op_float!(trunc);

impl_trunc_sat_s!(@from i32 @to i32, I32, trunc_sat_i32_s);
impl_trunc_sat_s!(@from i64 @to i64, I64, trunc_sat_i64_s);
impl_trunc_sat_u!(@from F32 @to u32 @but i32, I32, trunc_sat_from_f32_to_i32_u);
impl_trunc_sat_u!(@from F64 @to u32 @but i32, I32, trunc_sat_from_f64_to_i32_u);
impl_trunc_sat_u!(@from F32 @to u64 @but i64, I64, trunc_sat_from_f32_to_i64_u);
impl_trunc_sat_u!(@from F64 @to u64 @but i64, I64, trunc_sat_from_f64_to_i64_u);

impl_two_op_float!(min, @nan |left: f64, right: f64| left.min(right));
impl_two_op_float!(max, @nan |left: f64, right: f64| left.max(right));

impl_two_op_float!(copysign, |left: f64, right: f64| right.copysign(left));

fn eqz(left: Value) -> Value {
    match left {
        I32(v1) => I32((v1 == 0_i32) as i32),
        I64(v1) => I32((v1 == 0_i64) as i32),
        _ => panic!("Type mismatch during eqz"),
    }
}

fn nearest(v: Value) -> Value {
    match v {
        F32(v1) if v1.is_nan() => F32(f32::NAN),
        F64(v1) if v1.is_nan() => F64(f64::NAN),
        F32(v1) => {
            let fract = v1.fract().abs();

            let round = v1.round();
            if (fract - 0.5).abs() > f32::EPSILON {
                F32(round)
            } else if (round.rem(2.0) - 1.0).abs() < f32::EPSILON {
                F32(v1.floor())
            } else if (round.rem(2.0) - -1.0).abs() < f32::EPSILON {
                F32(v1.ceil())
            } else {
                F32(round)
            }
        }
        F64(v1) => {
            let fract = v1.fract().abs();

            let round = v1.round();
            if (fract - 0.5).abs() > f64::EPSILON {
                F64(round)
            } else if (round.rem(2.0) - 1.0).abs() < f64::EPSILON {
                F64(v1.floor())
            } else if (round.rem(2.0) - -1.0).abs() < f64::EPSILON {
                F64(v1.ceil())
            } else {
                F64(round)
            }
        }
        _ => panic!("Type mismatch during nearest"),
    }
}

fn reinterpret(v: Value) -> Value {
    match v {
        I32(k) => F32(f32::from_bits(k as u32)),
        I64(k) => F64(f64::from_bits(k as u64)),
        F32(k) => I32(i32::from_le(k.to_bits() as i32)),
        F64(k) => I64(i64::from_le(k.to_bits() as i64)),
    }
}

/// Returns Err when paging failed
/// Returns new length in pages
/// https://webassembly.github.io/spec/core/exec/modules.html#growing-memories
fn grow_memory(instance: &mut MemoryInstance, n: usize) -> Result<usize, ()> {
    if n == 0 {
        return Ok(instance.data.len() / PAGE_SIZE);
    }

    let len = n + instance.data.len();

    match instance.max {
        None => {
            if len / PAGE_SIZE > PAGE_SIZE * PAGE_SIZE as usize {
                error!("Length exceeded. Too many memory pages");
                return Err(());
            }
        }
        Some(max) => {
            debug!("Checking limit len {} < max {}", len / PAGE_SIZE, max);
            if len / PAGE_SIZE > max as usize {
                error!("Memory growing failed. Limit exceded");
                return Err(());
            }

            debug!(
                "Checking limit len {} + n {} < max {}",
                len / PAGE_SIZE,
                n,
                max
            );
            if len / PAGE_SIZE + n > max as usize {
                error!("Memory growing failed. Limit exceded");
                return Err(());
            }
        }
    }

    let new_length = instance.data.len() + (n as usize) * PAGE_SIZE;
    debug!("Resize by {} bytes", new_length);

    let extension = vec![0u8; (n as usize) * PAGE_SIZE];

    instance.data.extend_from_slice(&extension);

    //instance.data.resize(new_length, 0u8);
    //.resize(instance.data.len() + (n as usize) * PAGE_SIZE, 0u8);

    Ok(new_length / PAGE_SIZE)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variable {
    pub mutable: bool, //Actually, there is a `Mut` enum. TODO check if makes sense to use it
    pub val: Value,
}

#[derive(Debug, PartialEq)]
pub enum StackContent {
    Value(Value),
    Frame(Frame),
    Label(Label),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Label {
    arity: Arity,
}

#[derive(Debug)]
pub struct Frame {
    pub arity: u32,
    pub locals: Vec<Value>,
    //pub module_instance: Weak<RefCell<ModuleInstance>>,
}

impl PartialEq for Frame {
    fn eq(&self, other: &Self) -> bool {
        self.arity == other.arity && self.locals == other.locals
    }
}

#[derive(Debug, Clone)]
pub struct ModuleInstance {
    pub start: u32,
    pub code: Vec<FunctionBody>,
    pub fn_types: Vec<FunctionSignature>,
    pub funcaddrs: Vec<FuncIdx>,
    pub tableaddrs: Vec<TableIdx>,
    pub memaddrs: Vec<MemoryIdx>,
    pub globaladdrs: Vec<GlobalIdx>,
    pub exports: Vec<ExportInstance>,
}

#[derive(Debug)]
pub struct Store {
    pub funcs: Vec<FuncInstance>,
    pub tables: Vec<TableInstance>,
    pub memory: Vec<MemoryInstance>,
    pub stack: Vec<StackContent>,
    pub globals: Vec<Variable>, //=GlobalInstance
}

#[derive(Debug, Clone)]
pub struct FuncInstance {
    //FIXME Add HostFunc
    pub ty: FunctionSignature,
    //pub module: Weak<RefCell<ModuleInstance>>,
    pub code: FunctionBody,
}

#[derive(Debug, Clone)]
pub struct TableInstance {
    pub elem: Vec<Option<FuncIdx>>,
    pub max: Option<u32>,
}

#[derive(Clone)]
pub struct MemoryInstance {
    pub data: Vec<u8>,
    pub max: Option<u32>,
}

impl StackContent {
    pub fn is_value(&self) -> bool {
        match self {
            StackContent::Value(_) => true,
            _ => false,
        }
    }

    pub fn is_label(&self) -> bool {
        match self {
            StackContent::Label(_) => true,
            _ => false,
        }
    }
}

/// Overwritten debug implementation
/// Because `data` can have a lot of entries, which
/// can be a problem when printing
impl fmt::Debug for MemoryInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MemoryInstance")
            .field("data (only length)", &self.data.len())
            .field("max", &self.max)
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExportInstance {
    pub name: String,
    pub value: ExternalKindType, //TODO maybe drop the Type in name?
}

impl Into<ExportInstance> for &ExportEntry {
    fn into(self) -> ExportInstance {
        ExportInstance {
            name: self.name.clone(),
            value: self.kind,
        }
    }
}

/*
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum ExternalVal {
    Func(FuncIdx),
    Table(TableIdx),
    Mem(MemoryIdx),
    Global(GlobalIdx),
}
*/

macro_rules! fetch_unop {
    ($stack: expr) => {{
        debug!("Popping {:?}", $stack.last());
        let v1 = match $stack.pop().unwrap() {
            Value(v) => v,
            x => panic!("Top of stack was not a value, but instead {:?}", x),
        };
        (v1)
    }};
}

macro_rules! fetch_binop {
    ($stack: expr) => {{
        let v1 = fetch_unop!($stack);
        let v2 = fetch_unop!($stack);

        (v1, v2)
    }};
}

macro_rules! load_memory {
    ($self:expr, $arg:expr, $size:expr, $ty:ty, $variant:expr) => {
        let v1 = fetch_unop!($self.store.stack);

        if let I32(v) = v1 {
            let ea = (v + $arg.offset as i32) as usize;

            let module = &$self.module;

            let addr = module.memaddrs.get(0).expect("No memory address found");

            let instance = &$self.store.memory[*addr as usize];

            debug!("instance {:?}", instance);
            debug!("Range {:?}", ea..ea + $size);
            debug!("part {:?}", &instance.data[ea..ea + $size]);

            let mut b = vec![0; $size];
            b.copy_from_slice(&instance.data[ea..ea + $size]);
            assert!(b.len() == $size);

            debug!("b {:?}", b);

            unsafe {
                //Convert [u8] to [number]
                let c = &*(b.as_slice() as *const [u8] as *const [$ty]);
                debug!("c is {:?}", c);

                $self.store.stack.push(StackContent::Value($variant(c[0])));
            }
        } else {
            panic!("Expected I32, found something else");
        }
    };
}

macro_rules! load_memorySX {
    ($self:expr, $arg:expr, $size:expr, $ty:ty, $variant:expr, $cast_ty:ty) => {
        let v1 = fetch_unop!($self.store.stack);

        if let I32(v) = v1 {
            let ea = (v + $arg.offset as i32) as usize;

            let module = &$self.module;

            let addr = module.memaddrs.get(0).expect("No memory address found");

            let instance = &$self.store.memory[*addr as usize];

            debug!("instance {:?}", instance);
            debug!("Range {:?}", ea..ea + $size);
            debug!("part {:?}", &instance.data[ea..ea + $size]);

            let mut b = vec![0; $size];
            b.copy_from_slice(&instance.data[ea..ea + $size]);
            assert!(b.len() == $size);

            debug!("b {:?}", b);

            unsafe {
                // Convert [u8] to [number]
                let c = &*(b.as_slice() as *const [u8] as *const [$ty]);
                debug!("c is {:?}", c);

                // THIS IS DIFFERENT THAN `load_memory!`

                let c2 = c[0] as $cast_ty;

                $self
                    .store
                    .stack
                    .push(StackContent::Value($variant(c2.into())));

                // END
            }
        } else {
            panic!("Expected I32, found something else");
        }
    };
}

macro_rules! store_memory {
    ($self:expr, $arg:expr, $size:expr, $ty:ty, $variant:ident) => {
        let k = fetch_unop!($self.store.stack);
        let v1 = fetch_unop!($self.store.stack);

        if let $variant(t) = k {
            if let I32(v) = v1 {
                let ea = (v + $arg.offset as i32) as usize;

                let module = &$self.module;

                let addr = module.memaddrs.get(0).expect("No memory address found");

                let instance = &mut $self.store.memory[*addr as usize];

                let mut bytes = t.to_le_bytes();

                instance.data[ea..ea + $size].swap_with_slice(&mut bytes);
            } else {
                panic!("Expected I32, found something else");
            }
        } else {
            panic!("Expected a different value on the stack");
        }
    };
}

macro_rules! store_memoryN {
    ($self:expr, $arg:expr, $size:expr, $ty:ty, $variant:ident, $new_ty:ty, $N:expr) => {
        let k = fetch_unop!($self.store.stack);
        let v1 = fetch_unop!($self.store.stack);

        if let $variant(t) = k {
            if let I32(v) = v1 {
                let ea = (v + $arg.offset as i32) as usize;

                let module = &$self.module;

                let addr = module.memaddrs.get(0).expect("No memory address found");

                let instance = &mut $self.store.memory[*addr as usize];

                if instance.data.len() < ea + ($N / 8) {
                    panic!("Offset is corrupt");
                }

                let mut bytes = t.to_le_bytes();

                instance.data[ea..ea + $size].swap_with_slice(&mut bytes[0..($N / 8)]);
            } else {
                panic!("Expected I32, found something else");
            }
        } else {
            panic!("Expected a different value on the stack");
        }
    };
}

macro_rules! convert {
    ($self:expr, $val:ident, $from_ctr:ident, $to_ctr:ident, $to:ident) => {
        match $val {
            $from_ctr(i) => $self.store.stack.push(Value($to_ctr(i as $to))),
            x => return Err(anyhow!("Expected $from_ctr on stack but found {:?}", x)),
        }
    };
    ($self:expr, $val:ident, $from_ctr:ident, $to_ctr:ident, $to:ident, $intermediate:ident) => {
        match $val {
            $from_ctr(i) => $self
                .store
                .stack
                .push(Value($to_ctr(i as $intermediate as $to))),
            x => return Err(anyhow!("Expected $from_ctr on stack but found {:?}", x)),
        }
    };
}

impl ModuleInstance {
    pub fn new(m: &Module) -> Self {
        let mut mi = ModuleInstance {
            start: 0,
            code: Vec::new(),
            fn_types: Vec::new(),
            funcaddrs: Vec::new(),
            tableaddrs: Vec::new(),
            memaddrs: Vec::new(),
            globaladdrs: Vec::new(),
            exports: Vec::new(),
        };
        for section in m.sections.iter() {
            match section {
                Section::Code(CodeSection { entries: x }) => {
                    mi.code = x.clone();
                }
                Section::Type(TypeSection { entries: x }) => {
                    mi.fn_types = x.clone();
                }
                _ => {}
            }
        }

        mi
    }
}

impl Engine {
    pub fn new(mi: ModuleInstance, module: &Module) -> Self {
        let mut e = Engine {
            module: mi,
            started: false,
            store: Store {
                funcs: Vec::new(),
                tables: Vec::new(),
                stack: Vec::new(),
                globals: Vec::new(),
                memory: Vec::new(),
            },
        };

        debug!("before allocate {:#?}", e);
        e.allocate(module);
        debug!("after allocate {:#?}", e);

        e
    }

    fn allocate(&mut self, m: &Module) {
        info!("Allocation");
        crate::allocation::allocate(m, &mut self.module, &mut self.store)
            .expect("Allocation failed");
    }

    pub fn instantiation(&mut self, m: &Module) -> Result<()> {
        info!("Instantiation");
        let start_function = crate::instantiation::instantiation(m, &self.module, &mut self.store)?;

        if let Some(func_addr) = start_function {
            debug!("Invoking start function with {:?}", func_addr);
            self.invoke_function(func_addr, vec![])?;
        }

        Ok(())
    }

    /// Take only exported functions into consideration
    pub fn invoke_exported_function(&mut self, idx: u32, args: Vec<Value>) -> Result<()> {
        debug!("invoke_exported_function {:?}", idx);
        let k = {
            let x = &self.module;

            debug!("x's element {:?}", x.exports.get(idx as usize));

            let w = x
                .exports
                .get(idx as usize)
                .expect("Exported function not found or found something else");

            w.value
        };

        debug!("Exports {:#?}", k);

        match k {
            ExternalKindType::Function { ty } => {
                let func_addr = *self
                    .module
                    .funcaddrs
                    .get(ty as usize)
                    .ok_or_else(|| anyhow!("Function not found"))?;

                self.invoke_function(func_addr, args)?;
            }
            _ => {
                return Err(anyhow!("Exported function not found"));
            }
        }

        Ok(())
    }

    pub fn invoke_exported_function_by_name(&mut self, name: &str, args: Vec<Value>) -> Result<()> {
        let idx = self
            .module
            .exports
            .iter()
            .position(|e| e.name == name)
            .expect("Function not found");
        self.invoke_exported_function(idx as u32, args)?;

        Ok(())
    }

    pub(crate) fn invoke_function(&mut self, idx: u32, args: Vec<Value>) -> Result<()> {
        self.check_parameters_of_function(idx, &args);

        let t = &self.store.funcs[idx as usize].ty;
        let lc = match self.store.funcs[idx as usize].code.locals.get(0) {
            Some(fb) => fb.count as usize,
            None => 0,
        };

        let mut locals = args;

        if locals.len() < lc {
            locals.resize(lc, I32(0));
        }

        self.store.stack.push(Frame(Frame {
            arity: t.return_types.len() as u32,
            locals,
            //module_instance: Rc::downgrade(&self.module),
        }));

        trace!("stack before invoking {:#?}", self.store.stack);

        debug!("Invoking function");
        self.run_function(idx)
            .with_context(|| format!("Function with id {} failed", idx))?;

        Ok(())
    }

    fn local_set(&mut self, idx: &u32, fr: &mut Frame) -> Result<()> {
        debug!("OP_LOCAL_SET {:?}", idx);
        debug!("locals {:#?}", fr.locals);

        match self.store.stack.pop() {
            Some(Value(v)) => {
                match fr.locals.get_mut(*idx as usize) {
                    Some(k) => *k = v, //Exists replace
                    None => {
                        //Does not exists; push
                        fr.locals.push(v)
                    }
                }
            }
            Some(x) => panic!("Expected value but found {:?}", x),
            None => panic!("Empty stack during local.set"),
        }

        Ok(())
    }

    fn check_parameters_of_function(&self, idx: u32, args: &[Value]) {
        let fn_types = self
            .store
            .funcs
            .get(idx as usize)
            .expect("Function not found")
            .ty
            .param_types
            .iter();

        let argtypes = args.iter().map(|w| match *w {
            Value::I32(_) => ValueType::I32,
            Value::I64(_) => ValueType::I64,
            Value::F32(_) => ValueType::F32,
            Value::F64(_) => ValueType::F64,
        });

        let len_1 = fn_types.len();
        let len_2 = argtypes.len();

        // Check if `fn_types` and `argtypes` are elementwise equal
        let is_same = fn_types.zip(argtypes).map(|(x, y)| *x == y).all(|w| w);

        if !is_same || len_1 != len_2 {
            panic!("Function expected different parameters!");
        }
    }

    #[allow(clippy::cognitive_complexity)]
    pub(crate) fn run_function(&mut self, idx: u32) -> Result<()> {
        debug!("Running function {:?}", idx);

        //FIXME this `.clone` is extremly expensive!!!
        // But there is a problem
        // Because, we iterate over the borrowed iterator,
        // we cannot easily run the block
        let f = &self.module.code[idx as usize].clone();

        let mut fr = self.get_frame()?;

        debug!("frame {:#?}", fr);

        self.run_instructions(&mut fr, &mut f.code.iter())?;

        // implicit return
        debug!("Implicit return (arity {:?})", fr.arity);

        debug!("Stack before function return {:#?}", self.store.stack);

        let mut ret = Vec::new();
        for _ in 0..fr.arity {
            debug!("Popping {:?}", self.store.stack.last());
            match self.store.stack.pop() {
                Some(Value(v)) => ret.push(Value(v)),
                Some(x) => {
                    return Err(anyhow!("Expected value but found {:?}", x));
                }
                None => {} //None => panic!("Unexpected empty stack!"),
            }
        }

        debug!("Popping frames");
        while let Some(Frame(_)) = self.store.stack.last() {
            debug!("Removing {:?}", self.store.stack.last());
            self.store.stack.pop();
        }

        while let Some(val) = ret.pop() {
            self.store.stack.push(val);
        }

        debug!("Stack after function return {:#?}", self.store.stack);

        Ok(())
    }

    #[allow(clippy::cognitive_complexity)]
    fn run_instructions<'a>(
        &mut self,
        fr: &mut Frame,
        instructions: &'a mut impl std::iter::Iterator<Item = &'a Instruction>,
    ) -> Result<InstructionOutcome> {
        let mut ip = 0;
        for instruction in instructions {
            debug!("Evaluating instruction {:?}", instruction);
            match &instruction {
                Var(OP_LOCAL_GET(idx)) => {
                    if let Some(val) = fr.locals.get(*idx as usize) {
                        self.store.stack.push(Value(val.clone()));
                        debug!("LOCAL_GET at {} is {:?}", idx, fr.locals[*idx as usize]);
                        debug!("locals {:#?}", fr.locals);
                    } else {
                        return Err(anyhow!(
                            "Trying to access locals ({}), but out of bounds (length {})",
                            idx,
                            fr.locals.len()
                        ));
                    }
                }
                Var(OP_LOCAL_SET(idx)) => {
                    self.local_set(idx, fr)?;
                    debug!("locals {:#?}", fr.locals);
                }
                Var(OP_LOCAL_TEE(idx)) => {
                    debug!("OP_LOCAL_TEE {:?}", idx);

                    let value = match self.store.stack.pop() {
                        Some(StackContent::Value(v)) => v,
                        Some(x) => {
                            return Err(anyhow!("Expected value but found {:?}", x));
                        }
                        None => {
                            return Err(anyhow!("Empty stack during local.tee"));
                        }
                    };

                    self.store.stack.push(StackContent::Value(value));
                    self.store.stack.push(StackContent::Value(value));

                    self.local_set(idx, fr)?;

                    debug!("stack {:?}", self.store.stack);
                    debug!("locals {:#?}", fr.locals);
                }
                Var(OP_GLOBAL_GET(idx)) => {
                    self.store
                        .stack
                        .push(Value(self.store.globals[*idx as usize].val));

                    debug!("globals {:#?}", self.store.globals);
                }
                Var(OP_GLOBAL_SET(idx)) => match self.store.stack.pop() {
                    Some(Value(v)) => {
                        if !self.store.globals[*idx as usize].mutable {
                            return Err(anyhow!("Attempting to modify a immutable global"));
                        }
                        self.store.globals[*idx as usize].val = v;
                        debug!("globals {:#?}", self.store.globals);
                    }
                    Some(x) => {
                        return Err(anyhow!("Expected value but found {:?}", x));
                    }
                    None => {
                        return Err(anyhow!("Empty stack during local.tee"));
                    }
                },
                Num(OP_I32_CONST(v)) => {
                    debug!("OP_I32_CONST: pushing {} to stack", v);
                    self.store.stack.push(Value(I32(*v)));
                    debug!("stack {:#?}", self.store.stack);
                }
                Num(OP_I64_CONST(v)) => {
                    debug!("OP_I64_CONST: pushing {} to stack", v);
                    self.store.stack.push(Value(I64(*v)))
                }
                Num(OP_F32_CONST(v)) => {
                    debug!("OP_F32_CONST: pushing {} to stack", v);
                    self.store.stack.push(Value(F32(*v)))
                }
                Num(OP_F64_CONST(v)) => {
                    debug!("OP_F64_CONST: pushing {} to stack", v);
                    self.store.stack.push(Value(F64(*v)))
                }
                Num(OP_F32_COPYSIGN) => {
                    let (z1, z2) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(copysign(z1, z2)))
                }
                Num(OP_F64_COPYSIGN) => {
                    let (z1, z2) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(copysign(z1, z2)))
                }
                Num(OP_I32_ADD) | Num(OP_I64_ADD) | Num(OP_F32_ADD) | Num(OP_F64_ADD) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 + v2))
                }
                Num(OP_I32_SUB) | Num(OP_I64_SUB) | Num(OP_F32_SUB) | Num(OP_F64_SUB) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 - v2))
                }
                Num(OP_I32_MUL) | Num(OP_I64_MUL) | Num(OP_F32_MUL) | Num(OP_F64_MUL) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 * v2))
                }
                Num(OP_I32_DIV_S) | Num(OP_I64_DIV_S) | Num(OP_F32_DIV) | Num(OP_F64_DIV) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 / v2))
                }
                Num(OP_I32_DIV_U) | Num(OP_I64_DIV_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u32) / (x2 as u32)) as i32))),
                        (I64(x1), I64(x2)) => self
                            .store
                            .stack
                            .push(Value(I64(((x1 as u64) / (x2 as u64)) as i64))),
                        _ => return Err(anyhow!("Invalid types for DIV_U")),
                    }
                }
                Num(OP_I32_REM_S) | Num(OP_I64_REM_S) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 % v2))
                }
                Num(OP_I32_REM_U) | Num(OP_I64_REM_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u32) % (x2 as u32)) as i32))),
                        (I64(x1), I64(x2)) => self
                            .store
                            .stack
                            .push(Value(I64(((x1 as u64) % (x2 as u64)) as i64))),
                        _ => panic!("Invalid types for REM_U"),
                    }
                }
                Num(OP_I32_AND) | Num(OP_I64_AND) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 & v2))
                }
                Num(OP_I32_OR) | Num(OP_I64_OR) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 | v2))
                }
                Num(OP_I32_XOR) | Num(OP_I64_XOR) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 ^ v2))
                }
                Num(OP_I32_SHL) | Num(OP_I64_SHL) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 << v2))
                }
                Num(OP_I32_SHR_S) | Num(OP_I64_SHR_S) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(v1 >> v2))
                }
                Num(OP_I32_SHR_U) | Num(OP_I64_SHR_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => {
                            let k = x2 as u32 % 32;
                            self.store
                                .stack
                                .push(Value(I32(((x1 as u32).checked_shr(k)).unwrap_or(0) as i32)));
                        }
                        (I64(x1), I64(x2)) => {
                            let k = x2 as u64 % 64;
                            self.store
                                .stack
                                .push(Value(I64(
                                    ((x1 as u64).checked_shr(k as u32)).unwrap_or(0) as i64
                                )));
                        }
                        _ => return Err(anyhow!("Invalid types for SHR_U")),
                    }
                }
                Num(OP_I32_ROTL) | Num(OP_I64_ROTL) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(rotate_left(v1, v2)))
                }
                Num(OP_I32_ROTR) | Num(OP_I64_ROTR) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(rotate_right(v1, v2)))
                }
                Num(OP_I32_CLZ) | Num(OP_I64_CLZ) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(leading_zeros(v1)))
                }
                Num(OP_I32_CTZ) | Num(OP_I64_CTZ) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(trailing_zeros(v1)))
                }
                Num(OP_I32_POPCNT) | Num(OP_I64_POPCNT) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(count_ones(v1)))
                }
                Num(OP_I32_EQZ) | Num(OP_I64_EQZ) => {
                    let v1 = fetch_unop!(self.store.stack);

                    self.store.stack.push(Value(eqz(v1)))
                }
                Num(OP_I32_EQ) | Num(OP_I64_EQ) | Num(OP_F32_EQ) | Num(OP_F64_EQ) => {
                    let (v1, v2) = fetch_binop!(self.store.stack);
                    let res = v1 == v2;

                    if res {
                        self.store.stack.push(StackContent::Value(Value::I32(1)))
                    } else {
                        self.store.stack.push(StackContent::Value(Value::I32(0)))
                    }
                }
                Num(OP_I32_NE) | Num(OP_I64_NE) | Num(OP_F32_NE) | Num(OP_F64_NE) => {
                    let (v1, v2) = fetch_binop!(self.store.stack);
                    let res = v1 != v2;

                    if res {
                        self.store.stack.push(StackContent::Value(Value::I32(1)))
                    } else {
                        self.store.stack.push(StackContent::Value(Value::I32(0)))
                    }
                }
                Num(OP_I32_LT_S) | Num(OP_I64_LT_S) | Num(OP_F32_LT) | Num(OP_F64_LT) => {
                    // switch ordering because of stack layout
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(lt(v1, v2).convert(ValueType::I32)))
                }
                Num(OP_I32_LT_U) | Num(OP_I64_LT_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u32) < (x2 as u32)) as i32))),
                        (I64(x1), I64(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u64) < (x2 as u64)) as i32))),
                        _ => return Err(anyhow!("Invalid types for LT_U comparison")),
                    }
                }
                Num(OP_I32_GT_S) | Num(OP_I64_GT_S) | Num(OP_F32_GT) | Num(OP_F64_GT) => {
                    // switch ordering because of stack layout
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(gt(v1, v2).convert(ValueType::I32)))
                }
                Num(OP_I32_GT_U) | Num(OP_I64_GT_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u32) > (x2 as u32)) as i32))),
                        (I64(x1), I64(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u64) > (x2 as u64)) as i32))),
                        _ => return Err(anyhow!("Invalid types for GT_U comparison")),
                    }
                }
                Num(OP_I32_LE_S) | Num(OP_I64_LE_S) | Num(OP_F32_LE) | Num(OP_F64_LE) => {
                    // switch ordering because of stack layout
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(le(v1, v2).convert(ValueType::I32)))
                }
                Num(OP_I32_LE_U) | Num(OP_I64_LE_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u32) <= (x2 as u32)) as i32))),
                        (I64(x1), I64(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u64) <= (x2 as u64)) as i32))),
                        _ => return Err(anyhow!("Invalid types for LE_U comparison")),
                    }
                }
                Num(OP_I32_GE_S) | Num(OP_I64_GE_S) | Num(OP_F32_GE) | Num(OP_F64_GE) => {
                    // switch ordering because of stack layout
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(ge(v1, v2).convert(ValueType::I32)))
                }
                Num(OP_I32_GE_U) | Num(OP_I64_GE_U) => {
                    let (v2, v1) = fetch_binop!(self.store.stack);
                    match (v1, v2) {
                        (I32(x1), I32(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u32) >= (x2 as u32)) as i32))),
                        (I64(x1), I64(x2)) => self
                            .store
                            .stack
                            .push(Value(I32(((x1 as u64) >= (x2 as u64)) as i32))),
                        _ => return Err(anyhow!("Invalid types for GE_U comparison")),
                    }
                }
                Num(OP_F32_ABS) | Num(OP_F64_ABS) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(abs(v1)))
                }
                Num(OP_F32_NEG) | Num(OP_F64_NEG) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(neg(v1)))
                }
                Num(OP_F32_CEIL) | Num(OP_F64_CEIL) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(ceil(v1)))
                }
                Num(OP_F32_FLOOR) | Num(OP_F64_FLOOR) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(floor(v1)))
                }
                Num(OP_F32_TRUNC) | Num(OP_F64_TRUNC) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(trunc(v1)))
                }
                Num(OP_I32_TRUNC_SAT_F32_S) | Num(OP_I32_TRUNC_SAT_F64_S) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(trunc_sat_i32_s(v1)))
                }
                Num(OP_I64_TRUNC_SAT_F32_S) | Num(OP_I64_TRUNC_SAT_F64_S) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(trunc_sat_i64_s(v1)))
                }
                Num(OP_I32_TRUNC_SAT_F32_U) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(trunc_sat_from_f32_to_i32_u(v1)))
                }
                Num(OP_I32_TRUNC_SAT_F64_U) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(trunc_sat_from_f64_to_i32_u(v1)))
                }
                Num(OP_I64_TRUNC_SAT_F32_U) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(trunc_sat_from_f32_to_i64_u(v1)))
                }
                Num(OP_I64_TRUNC_SAT_F64_U) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store
                        .stack
                        .push(Value(trunc_sat_from_f64_to_i64_u(v1)))
                }
                Num(OP_F32_NEAREST) | Num(OP_F64_NEAREST) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(nearest(v1)))
                }
                Num(OP_F32_SQRT) | Num(OP_F64_SQRT) => {
                    let v1 = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(sqrt(v1)))
                }
                Num(OP_F32_MIN) | Num(OP_F64_MIN) => {
                    let (v1, v2) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(min(v1, v2)))
                }
                Num(OP_F32_MAX) | Num(OP_F64_MAX) => {
                    let (v1, v2) = fetch_binop!(self.store.stack);
                    self.store.stack.push(Value(max(v1, v2)))
                }
                Num(OP_I32_WRAP_I64) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, I32, i32);
                }
                Num(OP_I64_EXTEND_I32_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, I64, i64);
                }
                Num(OP_I64_EXTEND_I32_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, I64, i64, u32);
                }
                Num(OP_I64_TRUNC_F32_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F32, I64, i64);
                }
                Num(OP_I64_TRUNC_F64_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F64, I64, i64);
                }
                Num(OP_I64_TRUNC_F32_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F32, I64, i64, u64);
                }
                Num(OP_I64_TRUNC_F64_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F64, I64, i64, u64);
                }
                Num(OP_I32_TRUNC_F32_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F32, I32, i32);
                }
                Num(OP_I32_TRUNC_F64_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F64, I32, i32);
                }
                Num(OP_I32_TRUNC_F32_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F32, I32, i32, u32);
                }
                Num(OP_I32_TRUNC_F64_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F64, I32, i32, u32);
                }
                Num(OP_F32_DEMOTE_F64) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F64, F32, f32);
                }
                Num(OP_F64_PROMOTE_F32) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, F32, F64, f64);
                }
                Num(OP_F32_CONVERT_I32_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, F32, f32);
                }
                Num(OP_F64_CONVERT_I32_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, F64, f64);
                }
                Num(OP_F32_CONVERT_I64_S) => {
                    // Convert I64_S to F32
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, F32, f32);
                }
                Num(OP_F64_CONVERT_I64_S) => {
                    // Convert I64_S to F64
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, F64, f64);
                }
                Num(OP_F32_CONVERT_I32_U) => {
                    // Convert I32_S to F32
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, F32, f32, u32);
                }
                Num(OP_F64_CONVERT_I32_U) => {
                    // Convert I32_S to F64
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, F64, f64, u32);
                }
                Num(OP_F32_CONVERT_I64_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, F32, f32, u64);
                }
                Num(OP_F64_CONVERT_I64_U) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, F64, f64, u64);
                }
                Num(OP_I32_EXTEND8_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, I32, i32, i8);
                }
                Num(OP_I32_EXTEND16_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I32, I32, i32, i16);
                }
                Num(OP_I64_EXTEND8_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, I64, i64, i8);
                }
                Num(OP_I64_EXTEND16_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, I64, i64, i16);
                }
                Num(OP_I64_EXTEND32_S) => {
                    let v = fetch_unop!(self.store.stack);
                    convert!(self, v, I64, I64, i64, i32);
                }
                Num(OP_I32_REINTERPRET_F32)
                | Num(OP_I64_REINTERPRET_F64)
                | Num(OP_F32_REINTERPRET_I32)
                | Num(OP_F64_REINTERPRET_I64) => {
                    let v = fetch_unop!(self.store.stack);
                    self.store.stack.push(Value(reinterpret(v)));
                }
                Param(OP_DROP) => {
                    debug!("OP_DROP");
                    let k = self.store.stack.pop();
                    debug!("Dropping {:?}", k);
                }
                Param(OP_SELECT) => {
                    debug!("OP_SELECT");
                    debug!("Popping {:?}", self.store.stack.last());
                    let c = match self.store.stack.pop() {
                        Some(Value(I32(x))) => x,
                        _ => return Err(anyhow!("Expected I32 on top of stack")),
                    };
                    let (v1, v2) = fetch_binop!(self.store.stack);
                    if c != 0 {
                        debug!("C is not 0 therefore, pushing {:?}", v2);
                        self.store.stack.push(Value(v2))
                    } else {
                        debug!("C is not 0 therefore, pushing {:?}", v1);
                        self.store.stack.push(Value(v1))
                    }
                }
                Mem(OP_I32_LOAD_8_u(arg)) => {
                    load_memorySX!(self, arg, 4, i32, I32, u8);
                }
                Mem(OP_I32_LOAD_16_u(arg)) => {
                    load_memorySX!(self, arg, 4, i32, I32, u16);
                }
                Mem(OP_I32_LOAD_8_s(arg)) => {
                    load_memorySX!(self, arg, 4, i32, I32, i8);
                }
                Mem(OP_I32_LOAD_16_s(arg)) => {
                    load_memorySX!(self, arg, 4, i32, I32, i16);
                }
                Mem(OP_I32_LOAD(arg)) => {
                    load_memory!(self, arg, 4, i32, I32);
                }
                Mem(OP_I64_LOAD(arg)) => {
                    load_memory!(self, arg, 8, i64, I64);
                }
                Mem(OP_I64_LOAD_8_u(arg)) => {
                    load_memorySX!(self, arg, 8, i64, I64, u8);
                }
                Mem(OP_I64_LOAD_16_u(arg)) => {
                    load_memorySX!(self, arg, 8, i64, I64, u16);
                }
                Mem(OP_I64_LOAD_32_u(arg)) => {
                    load_memorySX!(self, arg, 8, i64, I64, u32);
                }
                Mem(OP_I64_LOAD_8_s(arg)) => {
                    load_memorySX!(self, arg, 8, i64, I64, i8);
                }
                Mem(OP_I64_LOAD_16_s(arg)) => {
                    load_memorySX!(self, arg, 8, i64, I64, i16);
                }
                Mem(OP_I64_LOAD_32_s(arg)) => {
                    load_memorySX!(self, arg, 8, i64, I64, i32);
                }
                Mem(OP_F32_LOAD(arg)) => {
                    load_memory!(self, arg, 4, f32, F32);
                }
                Mem(OP_F64_LOAD(arg)) => {
                    load_memory!(self, arg, 8, f64, F64);
                }
                Mem(OP_I32_STORE(arg)) => {
                    store_memory!(self, arg, 4, i32, I32);
                }
                Mem(OP_I64_STORE(arg)) => {
                    store_memory!(self, arg, 8, i64, I64);
                }
                Mem(OP_F32_STORE(arg)) => {
                    store_memory!(self, arg, 4, f32, F32);
                }
                Mem(OP_F64_STORE(arg)) => {
                    store_memory!(self, arg, 8, f64, F64);
                }
                Mem(OP_I32_STORE_8(arg)) => {
                    store_memoryN!(self, arg, 1, i32, I32, i8, 8);
                }
                Mem(OP_I32_STORE_16(arg)) => {
                    store_memoryN!(self, arg, 2, i32, I32, i16, 16);
                }
                Mem(OP_I64_STORE_8(arg)) => {
                    store_memoryN!(self, arg, 1, i64, I64, i8, 8);
                }
                Mem(OP_I64_STORE_16(arg)) => {
                    store_memoryN!(self, arg, 2, i64, I64, i16, 16);
                }
                Mem(OP_I64_STORE_32(arg)) => {
                    store_memoryN!(self, arg, 4, i64, I64, i32, 32);
                }
                Mem(OP_MEMORY_SIZE) => {
                    let module = &self.module;
                    let addr = module
                        .memaddrs
                        .get(0)
                        .ok_or_else(|| anyhow!("No memory address found"))?;
                    let instance = &self.store.memory[*addr as usize];

                    let sz = instance.data.len() / PAGE_SIZE;

                    self.store.stack.push(Value(I32(sz as i32)));
                }
                Mem(OP_MEMORY_GROW) => {
                    let module = &self.module;
                    let addr = module
                        .memaddrs
                        .get(0)
                        .ok_or_else(|| anyhow!("No memory address found"))?;
                    let instance = &mut self.store.memory[*addr as usize];
                    let _sz = instance.data.len() / PAGE_SIZE;

                    if let Some(Value(I32(n))) = self.store.stack.pop() {
                        if n < 0 {
                            return Err(anyhow!("Memory grow expected n > 0, got {}", n));
                        }

                        /*

                        if let Some(max) = instance.max {
                            if err > max {
                                error!("Memory growing failed. Limit exceded");
                                self.store.stack.push(Value(I32(err as i32)));
                                continue;
                            }
                        }
                        */

                        match grow_memory(instance, n as usize) {
                            Err(()) => {
                                error!("Memory growing failed because paging failed.");
                                let err = u32::MAX;
                                debug!("New memory size {}", err);
                                self.store.stack.push(Value(I32(err as i32)));
                            }
                            Ok(_new_sz) => {
                                //debug!("Old memory size {} pages", _new_sz);
                                self.store.stack.push(Value(I32(_sz as i32)));
                            }
                        }
                    } else {
                        return Err(anyhow!("Unexpected stack element. Expected I32"));
                    }
                }
                Ctrl(OP_BLOCK(ty, block_instructions)) => {
                    debug!("OP_BLOCK {:?}", ty);

                    let arity = self.get_block_ty_arity(&ty)?;

                    let label = Label {
                        arity: arity as u32,
                    };

                    self.store.stack.push(StackContent::Label(label));

                    let outcome =
                        self.run_instructions(fr, &mut block_instructions.instructions.iter())?;

                    match outcome {
                        InstructionOutcome::BRANCH(0) => {}
                        InstructionOutcome::BRANCH(x) => {
                            self.exit_block()?;
                            return Ok(InstructionOutcome::BRANCH(x - 1));
                        }
                        InstructionOutcome::RETURN => {
                            return Ok(InstructionOutcome::RETURN);
                        }
                        InstructionOutcome::EXIT => {}
                    }

                    self.exit_block()?;
                }
                Ctrl(OP_LOOP(ty, block_instructions)) => {
                    debug!("OP_LOOP {:?}, {:?}", ty, block_instructions);

                    let arity = self.get_block_ty_arity(&ty)?;

                    let label = Label {
                        arity: arity as u32,
                    };

                    self.store.stack.push(StackContent::Label(label));

                    loop {
                        let outcome =
                            self.run_instructions(fr, &mut block_instructions.instructions.iter())?;

                        match outcome {
                            InstructionOutcome::BRANCH(0) => {
                                continue;
                            }
                            InstructionOutcome::BRANCH(x) => {
                                self.exit_block()?;
                                return Ok(InstructionOutcome::BRANCH(x - 1));
                            }
                            InstructionOutcome::RETURN => {
                                return Ok(InstructionOutcome::RETURN);
                            }
                            InstructionOutcome::EXIT => {
                                break;
                            }
                        }
                    }

                    self.exit_block()?;
                }
                Ctrl(OP_IF(ty, block_instructions_branch)) => {
                    debug!("OP_IF {:?}", ty);
                    let element = self.store.stack.pop();
                    debug!("Popping value {:?}", element);

                    if let Some(StackContent::Value(Value::I32(v))) = element {
                        let arity = self.get_block_ty_arity(&ty)?;

                        if v != 0 {
                            debug!("C is not zero, therefore branching");

                            let label = Label {
                                arity: arity as u32,
                            };

                            self.store.stack.push(StackContent::Label(label));

                            let outcome = self.run_instructions(
                                fr,
                                &mut block_instructions_branch.instructions.iter(),
                            )?;

                            match outcome {
                                InstructionOutcome::BRANCH(0) => {}
                                InstructionOutcome::BRANCH(x) => {
                                    self.exit_block()?;
                                    return Ok(InstructionOutcome::BRANCH(x - 1));
                                }
                                InstructionOutcome::RETURN => {
                                    return Ok(InstructionOutcome::RETURN);
                                }
                                InstructionOutcome::EXIT => {}
                            }

                            self.exit_block()?;
                        } else {
                            debug!("C is zero, therefore not branching");
                        }
                    } else {
                        panic!("Value must be i32.const. Instead {:#?}", element);
                    }
                }
                Ctrl(OP_IF_AND_ELSE(
                    ty,
                    block_instructions_branch_1,
                    block_instructions_branch_2,
                )) => {
                    debug!("OP_IF_AND_ELSE {:?}", ty);
                    if let Some(StackContent::Value(Value::I32(v))) = self.store.stack.pop() {
                        //let label_idx = self.get_label_count()?;
                        //let (arity, args) = self.get_block_params(&ty)?;
                        let arity = self.get_block_ty_arity(&ty)?;

                        let label = Label {
                            arity: arity as u32,
                        };

                        self.store.stack.push(StackContent::Label(label));
                        if v != 0 {
                            debug!("C is not zero, therefore branching (1)");

                            let outcome = self.run_instructions(
                                fr,
                                &mut block_instructions_branch_1.instructions.iter(),
                            )?;

                            match outcome {
                                InstructionOutcome::BRANCH(0) => {}
                                InstructionOutcome::BRANCH(x) => {
                                    self.exit_block()?;
                                    return Ok(InstructionOutcome::BRANCH(x - 1));
                                }
                                InstructionOutcome::RETURN => {
                                    return Ok(InstructionOutcome::RETURN);
                                }
                                InstructionOutcome::EXIT => {}
                            }
                        } else {
                            debug!("C is zero, therefore branching (2)");

                            let outcome = self.run_instructions(
                                fr,
                                &mut block_instructions_branch_2.instructions.iter(),
                            )?;

                            match outcome {
                                InstructionOutcome::BRANCH(0) => {}
                                InstructionOutcome::BRANCH(x) => {
                                    self.exit_block()?;
                                    return Ok(InstructionOutcome::BRANCH(x - 1));
                                }
                                InstructionOutcome::RETURN => {
                                    return Ok(InstructionOutcome::RETURN);
                                }
                                InstructionOutcome::EXIT => {}
                            }
                        }

                        self.exit_block()?;
                    } else {
                        panic!("Value must be i32.const");
                    }
                }
                Ctrl(OP_BR(label_idx)) => {
                    debug!("OP_BR {}", label_idx);

                    return Ok(InstructionOutcome::BRANCH(*label_idx));
                }
                Ctrl(OP_BR_IF(label_idx)) => {
                    debug!("OP_BR_IF {}", label_idx);
                    if let Some(StackContent::Value(Value::I32(c))) = self.store.stack.pop() {
                        debug!("c is {}", c);
                        if c != 0 {
                            debug!("Branching to {}", label_idx);
                            return Ok(InstructionOutcome::BRANCH(*label_idx));
                        } else {
                            debug!("Not Branching to {}", label_idx);
                        }
                    }
                }
                Ctrl(OP_BR_TABLE(table, default)) => {
                    debug!("OP_BR_TABLE {:?}, {:?}", table, default);
                    let ival = fetch_unop!(self.store.stack);
                    if let I32(index) = ival {
                        let label_idx = if (index as usize) < table.len() {
                            table[index as usize]
                        } else {
                            debug!("Using default case");
                            *default
                        };
                        return Ok(InstructionOutcome::BRANCH(label_idx));
                    } else {
                        panic!("invalid index type: {:?}", ival);
                    }
                }
                Ctrl(OP_CALL(idx)) => {
                    debug!("OP_CALL {:?}", idx);

                    trace!("fn_types: {:#?}", self.module.fn_types);
                    let t = self.store.funcs[*idx as usize].ty.clone();

                    let args = self
                        .store
                        .stack
                        .split_off(self.store.stack.len() - t.param_types.len())
                        .into_iter()
                        .map(Engine::map_stackcontent_to_value)
                        .collect::<Result<_>>()?;

                    self.invoke_function(*idx, args)?;
                }
                Ctrl(OP_CALL_INDIRECT(idx)) => {
                    debug!("OP_CALL_INDIRECT {:?}", idx);
                    let ta = self.module.tableaddrs[0];
                    let tab = &self.store.tables[ta as usize];

                    let i = match fetch_unop!(self.store.stack) {
                        I32(x) => x,
                        x => return Err(anyhow!("invalid index type: {:?}", x)),
                    };
                    if (i as usize) >= tab.elem.len() {
                        return Err(anyhow!(
                            "Attempt to perform indirect call to index larger than the table"
                        ));
                    }
                    trace!("Table: {:?}", tab.elem);

                    match tab.elem[i as usize] {
                        Some(a) => {
                            let f = self
                                .store
                                .funcs
                                .get(a as usize)
                                .expect("No function in store");

                            {
                                // Compare types
                                let m = &self.module;
                                let ty = m.fn_types.get(*idx as usize);
                                assert!(&f.ty == ty.expect("No type found"));
                            }

                            let args = self
                                .store
                                .stack
                                .split_off(self.store.stack.len() - f.ty.param_types.len())
                                .into_iter()
                                .map(Engine::map_stackcontent_to_value)
                                .collect::<Result<_>>()?;

                            self.invoke_function(a as u32, args)?;
                        }
                        None => panic!("Table not initilized at index {}", i),
                    }
                }
                Ctrl(OP_RETURN) | Ctrl(OP_END) => {
                    debug!("Return");
                    return Ok(InstructionOutcome::RETURN);
                }
                Ctrl(OP_NOP) => {}
                Ctrl(OP_UNREACHABLE) => return Err(anyhow!("Reached unreachable => trap!")),
                //x => return Err(anyhow!("Instruction {:?} not implemented", x)),
            }
            ip += 1;

            debug!("ip is now {}", ip);

            trace!("stack {:#?}", self.store.stack);
        }

        Ok(InstructionOutcome::EXIT)
    }

    /// Get the frame at the top of the stack
    fn get_frame(&mut self) -> Result<Frame> {
        debug!("get_frame");
        match self.store.stack.pop() {
            Some(Frame(fr)) => Ok(fr),
            Some(x) => Err(anyhow!("Expected frame but found {:?}", x)),
            None => Err(anyhow!("Empty stack on function call")),
        }
    }

    fn exit_block(&mut self) -> Result<()> {
        debug!("exit_block");

        let mut val_m = Vec::new();

        while let Some(Value(_v)) = self.store.stack.last() {
            val_m.push(self.store.stack.pop().unwrap());
        }

        debug!("values {:?}", val_m);

        if !self
            .store
            .stack
            .pop()
            .ok_or_else(|| anyhow!("Expected Label, but found nothing"))?
            .is_label()
        {
            return Err(anyhow!("Expected label, but it's not a label"));
        }

        self.store.stack.append(&mut val_m);

        Ok(())
    }

    fn get_block_ty_arity(&mut self, block_ty: &BlockType) -> Result<usize> {
        Ok(match block_ty {
            BlockType::Empty => 0,
            BlockType::ValueType(_) => 1,
            BlockType::ValueTypeTy(ty) => self
                .module
                .fn_types
                .get(*ty as usize)
                .ok_or_else(|| anyhow!("Trap"))?
                .return_types
                .len(),
        })
    }

    /// Maps `StackContent` to `Value`
    fn map_stackcontent_to_value(x: StackContent) -> Result<Value> {
        match x {
            Value(v) => Ok(v),
            other => Err(anyhow!("Expected value but found {:?}", other)),
        }
    }
}
