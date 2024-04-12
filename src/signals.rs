/// a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum ALUOp {
    LoadStoreOp = 0b00,
    BranchOp = 0b01,
    RegisterOp = 0b10,
    ImmediateOp = 0b11,
}

/// a 1 bit signal that tells the ALU whether to use the register value (0) or the immediate value (1) as the second operand.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum ALUSrc {
    Register = 0,
    Immediate = 1,
}

/// a 4 bit signal that tells the ALU what operation to perform.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
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

/// a 2 bit signal that specifies where the next PC should come from.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
#[repr(u8)]
pub enum PCSrc {
    #[default]
    /// The next PC value comes from PC + 4
    Next = 0b00,
    /// The next PC value comes from the branch target address
    BranchTarget = 0b01,
    /// The next PC value comes from the jump target address
    JumpTarget = 0b10,
}
