use anyhow::{bail, Result};
use ux::{u2, u3, u7};

use crate::signals::ALUControl;

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
pub fn alu_control_unit(alu_op: u2, funct3: Option<u3>, funct7: Option<u7>) -> Result<ALUControl> {
    Ok(match (u8::from(alu_op), funct3, funct7) {
        (0b00, _, _) => ALUControl::ADD,
        (0b01, _, _) => ALUControl::SUB,
        (0b10, Some(funct3), Some(funct7)) => match (u8::from(funct7), u8::from(funct3)) {
            (0b0000000, 0b000) => ALUControl::ADD,  // add
            (0b1000000, 0b000) => ALUControl::SUB,  // sub
            (0b0000000, 0b111) => ALUControl::AND,  // and
            (0b0000000, 0b110) => ALUControl::OR,   // or
            (0b0000000, 0b001) => ALUControl::SLL,  // sll
            (0b0000000, 0b010) => ALUControl::SLT,  // slt
            (0b0000000, 0b011) => ALUControl::SLTU, // sltu
            (0b0000000, 0b100) => ALUControl::XOR,  // xor
            (0b0000000, 0b101) => ALUControl::SRL,  // srl
            (0b0100000, 0b101) => ALUControl::SRA,  // sra
            _ => bail!("Invalid funct3 and funct7 combination"),
        },
        (0b11, Some(funct3), Some(funct7)) => match (u8::from(funct7), u8::from(funct3)) {
            (_, 0b000) => ALUControl::ADD,         // addi
            (_, 0b010) => ALUControl::SLT,         // slti
            (_, 0b011) => ALUControl::SLTU,        // sltui
            (_, 0b100) => ALUControl::XOR,         // xori
            (_, 0b110) => ALUControl::OR,          // ori
            (_, 0b111) => ALUControl::AND,         // andi
            (0b0000000, 0b001) => ALUControl::SLL, // slli
            (0b0000000, 0b101) => ALUControl::SRL, // srli
            (0b0100000, 0b101) => ALUControl::SRA, // srai
            _ => bail!("Invalid funct3 and funct7 combination"),
        },
        _ => unreachable!(),
    })
}

pub fn alu(alu_control: ALUControl, a: u32, b: u32) -> (bool, u32) {
    let result = match alu_control {
        ALUControl::ADD => a.wrapping_add(b),
        ALUControl::SUB => a.wrapping_sub(b),
        ALUControl::AND => a & b,
        ALUControl::OR => a | b,
        ALUControl::SLL => a << b,
        ALUControl::SLT => ((a as i32) < b as i32) as u32,
        ALUControl::SLTU => (a < b) as u32,
        ALUControl::XOR => a ^ b,
        ALUControl::SRL => a >> b,
        ALUControl::SRA => (a as i32 >> b) as u32,
    };

    (result == 0, result)
}
