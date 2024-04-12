//! Structs that represent the outputs of the various stages of the pipeline.
//!
//! later on, we will use these structs to implement the pipeline registers.

use crate::instruction::Instruction;

/// a string that holds a report of what happened in the CPU during a clock cycle.
pub type Report = String;

pub struct IF {
    // pub next_pc: u32,
    // branch_target: u32,
    // jump_target: u32,
    // pcsrc: PCSrc,
}

pub struct IFID {
    // pub next_pc: u32,
    pub instruction_code: u32,
}

pub struct IDEX {
    pub instruction: Instruction,
    // pub next_pc: u32,
    pub read_data_1: Option<u32>,
    pub read_data_2: Option<u32>,
    pub immediate: Immediate,
    // pub alu_op: ALUOp,
    // pub alu_src: ALUSrc,
    // pub pc_src: PCSrc,
}

pub struct EXMEM {
    pub instruction: Instruction,
    // pub next_pc: u32,
    pub alu_result: u32,
    // pub read_data_2: u32,
    // pub write_register: u4,
    // pub write_data: u32,
    // pub mem_to_reg: bool,
    // pub reg_write: bool,
}

pub struct MEMWB {
    pub instruction: Instruction,
    // pub next_pc: u32,
    // pub alu_result: u32,
    // pub read_data: u32,
    // pub write_register: u4,
    // pub write_data: u32,
    // pub mem_to_reg: bool,
    // pub reg_write: bool,
}

pub struct WB {
    // pub next_pc: u32,
    // pub alu_result: u32,
    // pub read_data: u32,
    // pub write_register: u4,
    // pub write_data: u32,
    // pub mem_to_reg: bool,
    // pub reg_write: bool,
}

pub enum Immediate {
    /// for I-type instructions
    SignedImmediate(i32),
    /// for S-type instructions
    AddressOffset(i32),
    /// for U-type instructions
    UpperImmediate(u32),
    /// for SB-type instructions
    BranchOffset(i32),
    /// for UJ-type instructions
    JumpOffset(i32),
    /// for all other instructions
    None,
}
