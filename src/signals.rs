use anyhow::Result;
use ux::u7;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a struct that holds the control signals that the Control Unit generates.
///
/// A decent chunk of these are actually entirely unnessary for this implementation, but are included nonetheless for completeness.
pub struct ControlSignals {
    /// tells the register file to write to the register specified by the instruction.
    pub reg_write: bool,
    /// The BranchJump signal is a 2 bit signal that tells the Branching and Jump Unit what type of branching to consider.
    pub branch_jump: BranchJump,
    /// The ALUSrcA signal is a 1 bit signal that tells the ALU whether to use the register value (0), the PC (1), or the constant 0 as the second operand.
    pub alu_src_a: ALUSrcA,
    /// The ALUSrcB signal is a 1 bit signal that tells the ALU whether to use the register value (0), the immediate value (1), or the constant 4 as the second operand.
    pub alu_src_b: ALUSrcB,
    /// The ALU operation signal is a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed.
    pub alu_op: ALUOp,
    /// The mem_write signal is a 1 bit signal that tells the data memory unit whether to write to memory.
    pub mem_write: bool,
    /// controls what source the write back stages uses.
    pub wb_src: WriteBackSrc,
    /// The mem_read signal is a 1 bit signal that tells the data memory unit whether to read from memory.
    pub mem_read: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed
pub enum ALUOp {
    /// The ALU should perform an ADD operation, this is the case for memory load and store instructions.
    #[default]
    ADD = 0b00,
    /// The ALU should perform an operation specified by the funct3 field of the instruction (which specifies the type of branching to perform).
    /// This is the case for SB-type instructions.
    BRANCH = 0b01,
    /// The ALU should perform an operation specified by the funct7 and funct3 fields of the instruction.
    /// This is the case for R-type and I-type instructions.
    FUNCT = 0b10,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 1 bit signal that tells the ALU whether to use the register value (0), the PC (1), or the constant 0 as the second operand.
pub enum ALUSrcA {
    #[default]
    Register = 0,
    PC = 1,
    Constant0 = 2,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 1 bit signal that tells the ALU whether to use the register value (0), the immediate value (1), or the constant 4 as the second operand.
pub enum ALUSrcB {
    #[default]
    Register = 0,
    Immediate = 1,
    Constant4 = 2,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 4 bit signal that tells the ALU what operation to perform.
pub enum ALUControl {
    AND = 0b0000,
    OR = 0b0001,
    #[default]
    ADD = 0b0010,
    SLL = 0b0011,
    SLT = 0b0100,
    SLTU = 0b0101,
    SUB = 0b0110,
    XOR = 0b0111,
    SRL = 0b1000,
    SRA = 0b1010,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a signal that specifies where the next PC should come from.
pub enum PCSrc {
    #[default]
    /// The next PC value comes from PC + 4
    Next,
    /// The next PC value comes from the branch target address,
    BranchTarget { offset: i32 },
    /// The next PC value comes from the jump target address
    JumpTarget { target: u32 },
}

impl PCSrc {
    /// returns the next PC value.
    pub fn next(&self, pc: u32) -> u32 {
        match self {
            PCSrc::Next => pc + 4,
            PCSrc::BranchTarget { offset } => pc.wrapping_add_signed(*offset),
            PCSrc::JumpTarget { target } => *target,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 2 bit control signal that tells the Branching and Jump Unit what type of branching to consider.
pub enum BranchJump {
    #[default]
    No = 0b00,
    Branch = 0b01,
    Jal = 0b10,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 2 bit control signal that tells the WB stage what source to write back to the register file.
pub enum WriteBackSrc {
    #[default]
    NA = 0b00,
    ALU = 0b01,
    Mem = 0b10,
    PC = 0b11,
}

/// Control Unit implementation
///
/// # Arguments
///
/// * `opcode` - the opcode of the instruction
///
/// # Returns
///
/// * `ControlSignals` - the control signals that the Control Unit generates
///
/// # Errors
///
/// * if the opcode is not recognized / not supported
///
/// # Description
///
/// the control unit considers 9 types of instructions:
///
/// 1. `lui` instruction
/// 2. `auipc` instruction
/// 3. `jal` instruction
/// 4. `jalr` instruction
/// 5. branch instructions
/// 6. load instructions
/// 7. store instructions
/// 8. R-type instructions
/// 9. I-type instructions
pub fn control_unit(opcode: u7) -> Result<ControlSignals> {
    match u8::from(opcode) {
        // lui
        0b0110111 => Err(anyhow::anyhow!("lui instruction not supported yet")),

        // auipc
        0b0010111 => Err(anyhow::anyhow!("auipc instruction not supported yet")),

        // jal
        0b1101111 => Ok(ControlSignals {
            reg_write: true,
            branch_jump: BranchJump::Jal,
            alu_src_a: ALUSrcA::PC,
            alu_src_b: ALUSrcB::Immediate,
            alu_op: ALUOp::ADD,
            mem_write: false,
            wb_src: WriteBackSrc::PC,
            mem_read: false,
        }),

        // jalr
        0b1100111 => Ok(ControlSignals {
            reg_write: true,
            branch_jump: BranchJump::Jal,
            alu_src_a: ALUSrcA::Register,
            alu_src_b: ALUSrcB::Immediate,
            alu_op: ALUOp::ADD,
            mem_write: false,
            wb_src: WriteBackSrc::PC,
            mem_read: false,
        }),

        // branch
        0b1100011 => Ok(ControlSignals {
            reg_write: false,
            branch_jump: BranchJump::Branch,
            alu_src_a: ALUSrcA::Register,
            alu_src_b: ALUSrcB::Register,
            alu_op: ALUOp::BRANCH,
            mem_write: false,
            wb_src: WriteBackSrc::NA,
            mem_read: false,
        }),

        // load
        0b0000011 => Ok(ControlSignals {
            reg_write: true,
            branch_jump: BranchJump::No,
            alu_src_a: ALUSrcA::Register,
            alu_src_b: ALUSrcB::Immediate,
            alu_op: ALUOp::ADD,
            mem_write: false,
            wb_src: WriteBackSrc::Mem,
            mem_read: true,
        }),

        // store
        0b0100011 => Ok(ControlSignals {
            reg_write: false,
            branch_jump: BranchJump::No,
            alu_src_a: ALUSrcA::Register,
            alu_src_b: ALUSrcB::Immediate,
            alu_op: ALUOp::ADD,
            mem_write: true,
            wb_src: WriteBackSrc::NA,
            mem_read: false,
        }),

        // R-type
        0b0110011 => Ok(ControlSignals {
            reg_write: true,
            branch_jump: BranchJump::No,
            alu_src_a: ALUSrcA::Register,
            alu_src_b: ALUSrcB::Register,
            alu_op: ALUOp::FUNCT,
            mem_write: false,
            wb_src: WriteBackSrc::ALU,
            mem_read: false,
        }),

        // I-type
        0b0010011 => Ok(ControlSignals {
            reg_write: true,
            branch_jump: BranchJump::No,
            alu_src_a: ALUSrcA::Register,
            alu_src_b: ALUSrcB::Immediate,
            alu_op: ALUOp::FUNCT,
            mem_write: false,
            wb_src: WriteBackSrc::ALU,
            mem_read: false,
        }),

        _ => Err(anyhow::anyhow!("opcode not recognized")),
    }
}
