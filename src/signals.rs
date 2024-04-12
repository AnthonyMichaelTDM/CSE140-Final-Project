use ux::u7;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a struct that holds the control signals that the Control Unit generates.
///
/// A decent chunk of these are actually entirely unnessary for this implementation, but are included nonetheless for completeness.
pub struct ControlSignals {
    /// tells the register file to write to the register specified by the instruction.
    pub reg_write: Option<bool>,
    /// The branch signal is a 1 bit signal that controls whether a branch *can* be taken. (It is not the branch condition itself. That is determined by the ALU zero signal.)
    pub branch: Option<bool>,
    /// The ALUSrc signal is a 1 bit signal that tells the ALU whether to use the register value (0) or the immediate value (1) as the second operand.
    pub alu_src: Option<ALUSrc>,
    /// The ALU operation signal is a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed.
    pub alu_op: Option<ALUOp>,
    /// The mem_write signal is a 1 bit signal that tells the data memory unit whether to write to memory.
    pub mem_write: Option<bool>,
    /// controls whether the write back stages uses the output of the data memory unit or the ALU.
    pub mem_to_reg: Option<bool>,
    /// The mem_read signal is a 1 bit signal that tells the data memory unit whether to read from memory.
    pub mem_read: Option<bool>,
    /// The PCSrc signal is a 2 bit signal that tells the cpu where to get the next PC value from.
    /// 00: PC + 4
    /// 01: branch_target
    /// 10: jump_target
    pub pc_src: PCSrc,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
/// a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed
pub enum ALUOp {
    /// The ALU should perform an ADD operation, this is the case for memory load and store instructions.
    ADD = 0b00,
    /// The ALU should perform a SUB operation, this is the case for branch instructions.
    SUB = 0b01,
    /// The ALU should perform an operation specified by the funct7 and funct3 fields of the instruction.
    /// This is the case for R-type and I-type instructions.
    FUNCT = 0b10,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
/// a 1 bit signal that tells the ALU whether to use the register value (0) or the immediate value (1) as the second operand.
pub enum ALUSrc {
    Register = 0,
    Immediate = 1,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
/// a 4 bit signal that tells the ALU what operation to perform.
pub enum ALUControl {
    ADD = 0b0010,
    SUB = 0b0110,
    AND = 0b0000,
    OR = 0b0001,
    SLL = 0b0011,
    SLT = 0b0100,
    SLTU = 0b0101,
    XOR = 0b0111,
    SRL = 0b1000,
    SRA = 0b1010,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
/// a 2 bit signal that specifies where the next PC should come from.
pub enum PCSrc {
    #[default]
    /// The next PC value comes from PC + 4
    Next = 0b00,
    /// The next PC value comes from the branch target address
    BranchTarget = 0b01,
    /// The next PC value comes from the jump target address
    JumpTarget = 0b10,
}

pub fn control_unit(_opcode: u7) -> ControlSignals {
    todo!()
}
