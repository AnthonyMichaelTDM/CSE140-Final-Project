use anyhow::{bail, Result};
use ux::{u1, u2, u3, u4, u7};

/// a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed
pub struct ALUOp();

impl ALUOp {
    pub const LOAD_STORE_OP: u2 = u2::new(0b00);
    pub const BRANCH_OP: u2 = u2::new(0b01);
    pub const REGISTER_OP: u2 = u2::new(0b10);
    pub const IMMEDIATE_OP: u2 = u2::new(0b11);
}

/// a 1 bit signal that tells the ALU whether to use the register value (0) or the immediate value (1) as the second operand.
pub struct ALUSrc();

impl ALUSrc {
    pub const REGISTER: u1 = u1::new(0);
    pub const IMMEDIATE: u1 = u1::new(1);
}

/// a 4 bit signal that tells the ALU what operation to perform.
pub struct ALUControl();

// only the first 4 are used in this project
impl ALUControl {
    pub const ADD: u4 = u4::new(0b0010);
    pub const SUB: u4 = u4::new(0b0110);
    pub const AND: u4 = u4::new(0b0000);
    pub const OR: u4 = u4::new(0b0001);
    pub const SLL: u4 = u4::new(0b0011);
    pub const SLT: u4 = u4::new(0b0100);
    pub const SLTU: u4 = u4::new(0b0101);
    pub const XOR: u4 = u4::new(0b0111);
    pub const SRL: u4 = u4::new(0b1000);
    pub const SRA: u4 = u4::new(0b1010);
}

/// This function mimics the ALU Control Unit in a risc-v processor, it takes in the ALU operation signal, the funct3 field of the instruction and the funct7 field of the instruction and returns the ALU control signal.
///
/// The ALU operation signal is a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed.
///
/// The funct3 and funct7 fields are used in combination with alu_op to determine the exact operation to be performed by the ALU.
///
/// This function is an implementation of the following Verilog module:
///
/// ```verilog,ignore
/// module ALUControl(
///     input [1:0] Aluop,
///     input funct7,[2:0] funct3,
///     output reg [3:0] Control
/// );
///     always @(*)
///     begin
///         case (Aluop)
///             2'b00 : Control <= 4'b0010;
///             2'b01 : Control <= 4'b0110;
///             2'b10 : case({funct7,funct3})
///                 4'b0000 : Control <= 4'b0010; // add
///                 4'b1000 : Control <= 4'b0110; // sub
///                 4'b0111 : Control <= 4'b0000; // and
///                 4'b0110 : Control <= 4'b0001; // or
///                 4'b0001 : Control <= 4'b0011; // sll
///                 4'b0010 : Control <= 4'b0100; // slt
///                 4'b0011 : Control <= 4'b0101; // sltu
///                 4'b0100 : Control <= 4'b0111; // xor
///                 4'b0101 : Control <= 4'b1000; // srl
///                 4'b1101 : Control <= 4'b1010; // sra
///                 default : Control <= 4'bxxxx;
///             endcase
///             2'b11 : case({funct7,funct3})
///             4'b0000 : Control <= 4'b0010; // addi
///             4'b0010 : Control <= 4'b0100; // slti
///             4'b0011 : Control <= 4'b0101; // sltui
///             4'b0100 : Control <= 4'b0111; // xori
///             4'b0110 : Control <= 4'b0001; // ori
///             4'b0111 : Control <= 4'b0000; // andi
///             4'b0001 : Control <= 4'b0011; // slli
///             4'b0101 : Control <= 4'b1000; // srli
///             4'b1101 : Control <= 4'b1010; // srai
///             default : Control <= 4'bxxxx;
///         endcase
///         endcase
///     end
/// endmodule
/// ```
pub fn alu_control_unit(alu_op: u2, funct3: Option<u3>, funct7: Option<u7>) -> Result<u4> {
    Ok(u4::new(match (u8::from(alu_op), funct3, funct7) {
        (0b00, _, _) => 0b0010,
        (0b01, _, _) => 0b0110,
        (0b10, Some(funct3), Some(funct7)) => match (u8::from(funct7), u8::from(funct3)) {
            (0b0000000, 0b000) => 0b0010, // add
            (0b1000000, 0b000) => 0b0110, // sub
            (0b0000000, 0b111) => 0b0000, // and
            (0b0000000, 0b110) => 0b0001, // or
            (0b0000000, 0b001) => 0b0011, // sll
            (0b0000000, 0b010) => 0b0100, // slt
            (0b0000000, 0b011) => 0b0101, // sltu
            (0b0000000, 0b100) => 0b0111, // xor
            (0b0000000, 0b101) => 0b1000, // srl
            (0b0100000, 0b101) => 0b1010, // sra
            _ => bail!("Invalid funct3 and funct7 combination"),
        },
        (0b11, Some(funct3), Some(funct7)) => match (u8::from(funct7), u8::from(funct3)) {
            (_, 0b000) => 0b0010,         // addi
            (_, 0b010) => 0b0100,         // slti
            (_, 0b011) => 0b0101,         // sltui
            (_, 0b100) => 0b0111,         // xori
            (_, 0b110) => 0b0001,         // ori
            (_, 0b111) => 0b0000,         // andi
            (0b0000000, 0b001) => 0b0011, // slli
            (0b0000000, 0b101) => 0b1000, // srli
            (0b0100000, 0b101) => 0b1010, // srai
            _ => bail!("Invalid funct3 and funct7 combination"),
        },
        _ => unreachable!(),
    }))
}
