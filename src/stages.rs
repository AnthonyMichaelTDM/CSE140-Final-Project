//! Structs that represent the outputs of the various stages of the pipeline.
//!
//! later on, we will use these structs to implement the pipeline registers.

use crate::{
    instruction::Instruction,
    registers::RegisterMapping,
    signals::{ControlSignals, PCSrc},
};

/// a string that holds a report of what happened in the CPU during a clock cycle.
pub type Report = String;

/// a struct that holds the values of the pipeline stage registers.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct StageRegisters {
    pub ifid: IfId,
    pub idex: IdEx,
    pub exmem: ExMem,
    pub memwb: MemWb,
    pub wb_stage: Wb,
}

/// The IF/ID pipeline stage register.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum IfId {
    /// the values that are passed from the IF stage to the ID stage.
    If {
        /// the machine code of the instruction that was fetched.
        instruction_code: u32,
        /// the program counter value of the instruction.
        pc: u32,
    },
    #[default]
    /// used to flush the pipeline.
    Flush,
}

/// The ID/EX pipeline stage register.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum IdEx {
    /// the values that are passed from the ID stage to the EX stage.
    Id {
        instruction: Instruction,
        rs1: Option<RegisterMapping>,
        read_data_1: Option<u32>,
        rs2: Option<RegisterMapping>,
        read_data_2: Option<u32>,
        immediate: Immediate,
        /// the program counter value of the instruction.
        pc: u32,
        control_signals: ControlSignals,
    },
    #[default]
    /// used to flush the pipeline.
    Flush,
    /// used to indicate a stall in the pipeline.
    Stall,
}

/// The EX/MEM pipeline stage register.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum ExMem {
    /// the values that are passed from the EX stage to the MEM stage.
    Ex {
        instruction: Instruction,
        alu_result: u32,
        /// This variable will be updated by Execute() function and used when deciding to use branch target address in the next cycle.
        /// The zero variable will be set to 1 by ALU when the computation result is zero and unset to 0 if otherwise.
        alu_zero: bool,
        read_data_2: Option<u32>,
        /// the program counter value of the instruction.
        pc: u32,
        /// the next program counter value.
        pc_src: PCSrc,
        control_signals: ControlSignals,
    },
    #[default]
    /// used to flush the pipeline.
    Flush,
}

/// The MEM/WB pipeline stage register.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum MemWb {
    /// the values that are passed from the MEM stage to the WB stage.
    Mem {
        instruction: Instruction,
        mem_read_data: Option<u32>,
        alu_result: u32,
        /// the program counter value of the instruction.
        pc: u32,
        control_signals: ControlSignals,
    },
    #[default]
    /// used to flush the pipeline.
    Flush,
}

/// used to store the value written to the register file in the WB stage, if any, for data forwarding
///
/// since we execute stages backwards, if we want to forward data from the MEM/WB stage to the ID/EX stage,
/// we need to store the value written to the register file in the WB stage.
/// Because otherwise, the value will be overwritten before we can forward it.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum Wb {
    /// information needed by the forwarding unit
    Mem {
        instruction: Instruction,
        wb_data: Option<u32>,
        control_signals: ControlSignals,
    },
    #[default]
    /// used to flush the pipeline.
    Flush,
}

/// An enum that represents the different types of immediate values in RISC-V instructions.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Immediate {
    /// for I-type and S-type instructions
    SignedImmediate(i32),
    /// for U-type instructions
    UpperImmediate(u32),
    /// for SB-type instructions
    BranchOffset(i32),
    /// for UJ-type instructions
    JumpOffset(i32),
    /// for all other instructions
    None,
}
