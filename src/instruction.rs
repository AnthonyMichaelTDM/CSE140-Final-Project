use ux::{i12, u20, u3, u7};

use crate::registers::RegisterMapping;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Instruction {
    RType {
        funct7: u7,
        rs2: RegisterMapping,
        rs1: RegisterMapping,
        funct3: u3,
        rd: RegisterMapping,
        opcode: u7,
    },
    IType {
        imm: i12,
        rs1: RegisterMapping,
        funct3: u3,
        opcode: u7,
    },
    SType {
        imm: i12,
        rs2: RegisterMapping,
        rs1: RegisterMapping,
        funct3: u3,
        opcode: u7,
    },
    SBType {
        imm: i12,
        rs2: RegisterMapping,
        rs1: RegisterMapping,
        funct3: u3,
        opcode: u7,
    },
    UType {
        imm: u20,
        rd: RegisterMapping,
        opcode: u7,
    },
    UJType {
        imm: u20,
        rd: RegisterMapping,
        opcode: u7,
    },
}
