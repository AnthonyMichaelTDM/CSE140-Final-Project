use anyhow::{bail, Result};
use ux::{i12, i13, u20, u21, u3, u5, u7};

use crate::registers::RegisterMapping;

/// An enum that represents the different types of instructions that can be executed by the CPU.
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
        /// only used for the shift instructions
        funct7: Option<u7>,
        /// only used for the shift instructions
        shamt: Option<u5>,
        imm: i12,
        rs1: RegisterMapping,
        funct3: u3,
        rd: RegisterMapping,
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
        imm: i13, // 12 bits stored in machine code + last bit is always 0
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
        imm: u21, // 20 bits stored in machine code + last bit is always 0
        rd: RegisterMapping,
        opcode: u7,
    },
}

impl Instruction {
    /// Convert a 32-bit machine code instruction into an `Instruction` enum variant.
    ///
    /// # Arguments
    ///
    /// * `machine_code` - the 32-bit machine code instruction
    ///
    /// # Returns
    ///
    /// * `Result<Instruction>` - The decoded `Instruction`, if the machine code is valid. Otherwise, an error is returned.
    ///
    /// # Errors
    ///
    /// This function will return an error if the machine code is invalid.
    #[allow(clippy::too_many_lines)]
    pub fn from_machine_code(machine_code: u32) -> Result<Self> {
        // extract the opcode
        let opcode: u7 = u7::new((machine_code & 0b111_1111) as u8);

        // fields that are common to most instructions
        // (or at least are extracted the same way in all instructions the fields are present in)
        // we defer propogating any errors in reading the register mappings until we know the instruction uses them
        let rd = RegisterMapping::try_from(((machine_code >> 7) & 0b11111) as u8);
        let rs1 = RegisterMapping::try_from(((machine_code >> 15) & 0b11111) as u8);
        let rs2 = RegisterMapping::try_from(((machine_code >> 20) & 0b11111) as u8);
        let funct3: u3 = u3::new(((machine_code >> 12) & 0b111) as u8);

        match u8::from(opcode) {
            // R-type instructions
            0b011_0011 // arithmetic instructions
            | 0b011_1011 // arithmetic instructions (word width (only available on RV64, not implemented))
            => {
                // mask out the fields
                let funct7: u7 = u7::new(((machine_code >> 25) & 0b111_1111) as u8);

                Ok(Self::RType {
                    funct7,
                    rs2: rs2?,
                    rs1: rs1?,
                    funct3,
                    rd: rd?,
                    opcode,
                })
            }
            // I-type instructions
            0b000_0011 // load instructions
            | 0b000_1111 // fence instructions (not implemented)
            | 0b001_0011 // arithmetic instructions
            | 0b001_1011 // arithmetic instructions (word width (only available on RV64, not implemented))
            | 0b110_0111 // jalr
            | 0b111_0011 // system instructions (not implemented)
            => {
                let (funct7, shamt) = match (u8::from(opcode), u8::from(funct3)) {
                    // shift operations
                    (0b001_0011, 0b001 | 0b101) => (
                        Some(u7::new(((machine_code >> 25) & 0b111_1111) as u8)),
                        Some(u5::new(((machine_code >> 20) & 0b11111) as u8)),
                    ),
                    // other i type ops
                    _ => (None, None),
                };

                // convert to i32 so that our shift operations are sign extended, and we're explicity okay with the possible wrap
                #[allow(clippy::cast_possible_wrap)]
                let machine_code: i32 = machine_code as i32;
                let imm: i12 =
                    /* extract the lowest 12 bits of the immediate from the machine code */
                    i12::new((machine_code >> 20) as i16 & 0b1111_1111_1111);

                Ok(Self::IType {
                    funct7,
                    shamt,
                    imm,
                    rs1: rs1?,
                    funct3,
                    rd: rd?,
                    opcode,
                })
            }
            // S-type instructions
            0b010_0011 => {
                // convert to i32 so that our shift operations are sign extended, and we're explicity okay with the possible wrap
                #[allow(clippy::cast_possible_wrap)]
                let machine_code: i32 = machine_code as i32;
                // only the lower 12 bits of the immediate are given, so we need to sign extend it to 32 bits
                let imm: i12 =
                    /* extract the lowest 12 bits of the immediate from the machine code */
                    i12::new((((machine_code >> 7) & 0b11111) as i16 | ((machine_code >> 20) as i16 & 0b1111_1110_0000)) << 4 >> 4);

                Ok(Self::SType {
                    imm,
                    rs2: rs2?,
                    rs1: rs1?,
                    funct3,
                    opcode,
                })
            }
            // SB-type instructions
            0b110_0011 => {
                // convert to i32 so that our shift operations are sign extended, and we're explicity okay with the possible wrap
                #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                let machine_code: i32 = machine_code as i32;
                #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
                let imm: i13 = i13::new(
                    ((
                        /* extract the lowest 12 bits of the immediate from the machine code */
                        (machine_code >> 31) << 12// 12th bit
                    | ((machine_code << 4) & 0b1000_0000_0000)// 11th bit
                    | ((machine_code >> 20) & 0b111_1110_0000)// 10th:5th bits
                    | ((machine_code >> 7) & 0b11110)
                        // 4th:1st bits, 0th bit is always 0
                    ) as i16)
                        << 3
                        >> 3,
                );

                Ok(Self::SBType {
                    imm,
                    rs2: rs2?,
                    rs1: rs1?,
                    funct3,
                    opcode,
                })
            }
            // U-type instructions
            0b001_0111 // auipc
            | 0b011_0111 // lui
            => {
                #[allow(clippy::cast_possible_wrap)]
                #[allow(clippy::cast_sign_loss)]
                let imm: u20 = u20::new((((machine_code & 0xFFFF_F000) as i32) >> 12) as u32);

                Ok(Self::UType {
                    imm,
                    rd: rd?,
                    opcode,
                })
            }
            // UJ-type instructions
            0b110_1111 => {
                let imm: u21 = u21::new(
                    ((machine_code >> 11) & 0b1_0000_0000_0000_0000_0000) // 20th bit
                    | (machine_code & 0b1111_1111_0000_0000_0000)// 19th:12th bits
                    | ((machine_code >> 9) & 0b1000_0000_0000)// 11th bit
                    | ((machine_code >> 20) & 0b111_1111_1110), // 10th:1st bits, 0th bit is always 0
                );

                Ok(Self::UJType {
                    imm,
                    rd: rd?,
                    opcode,
                })
            }
            // Unknown instruction
            _ => bail!(
                "Unknown OpCode: {:07b}\n machine code: {machine_code:#010x}",
                opcode
            ),
        }
    }

    /// Get the opcode of the instruction.
    ///
    /// # Returns
    ///
    /// * `u7` - the opcode of the instruction.
    #[must_use]
    pub const fn opcode(&self) -> u7 {
        match self {
            Self::RType { opcode, .. }
            | Self::IType { opcode, .. }
            | Self::SType { opcode, .. }
            | Self::SBType { opcode, .. }
            | Self::UType { opcode, .. }
            | Self::UJType { opcode, .. } => *opcode,
        }
    }

    /// Get the funct3 field of the instruction.
    ///
    /// # Returns
    ///
    /// * `Option<u3>` - the funct3 field of the instruction, if it has one.
    #[must_use]
    pub const fn funct3(&self) -> Option<u3> {
        match self {
            Self::RType { funct3, .. }
            | Self::IType { funct3, .. }
            | Self::SType { funct3, .. }
            | Self::SBType { funct3, .. } => Some(*funct3),
            Self::UType { .. } | Self::UJType { .. } => None,
        }
    }

    /// Get the funct7 field of the instruction.
    ///
    /// # Returns
    ///
    /// * `Option<u7>` - the funct7 field of the instruction, if it has one.
    #[must_use]
    pub const fn funct7(&self) -> Option<u7> {
        match self {
            Self::RType { funct7, .. }
            | Self::IType {
                funct7: Some(funct7),
                ..
            } => Some(*funct7),
            _ => None,
        }
    }

    /// Get the shamt field of the instruction.
    ///
    /// # Returns
    ///
    /// * `Option<u5>` - the shamt field of the instruction, if it has one.
    #[must_use]
    pub const fn shamt(&self) -> Option<u5> {
        match self {
            Self::IType {
                shamt: Some(shamt), ..
            } => Some(*shamt),
            _ => None,
        }
    }

    /// Get the rd field of the instruction.
    ///
    /// # Returns
    ///
    /// * `Option<RegisterMapping>` - the rd field of the instruction, if it has one.
    #[must_use]
    pub const fn rd(&self) -> Option<RegisterMapping> {
        match self {
            Self::RType { rd, .. }
            | Self::IType { rd, .. }
            | Self::UType { rd, .. }
            | Self::UJType { rd, .. } => Some(*rd),
            Self::SType { .. } | Self::SBType { .. } => None,
        }
    }

    /// Get the rs1 field of the instruction.
    ///
    /// # Returns
    ///
    /// * `Option<RegisterMapping>` - the rs1 field of the instruction, if it has one.
    #[must_use]
    pub const fn rs1(&self) -> Option<RegisterMapping> {
        match self {
            Self::RType { rs1, .. }
            | Self::IType { rs1, .. }
            | Self::SType { rs1, .. }
            | Self::SBType { rs1, .. } => Some(*rs1),
            Self::UType { .. } | Self::UJType { .. } => None,
        }
    }

    /// Get the rs2 field of the instruction.
    ///
    /// # Returns
    ///
    /// * `Option<RegisterMapping>` - the rs2 field of the instruction, if it has one.
    #[must_use]
    pub const fn rs2(&self) -> Option<RegisterMapping> {
        match self {
            Self::RType { rs2, .. } | Self::SType { rs2, .. } | Self::SBType { rs2, .. } => {
                Some(*rs2)
            }
            Self::IType { .. } | Self::UType { .. } | Self::UJType { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use anyhow::Result;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_add() -> Result<()> {
        let machine_code: u32 = 0b0000_0000_0011_0010_0000_0010_1011_0011;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::RType {
                funct7: u7::new(0),
                rs2: RegisterMapping::Gp,
                rs1: RegisterMapping::Tp,
                funct3: u3::new(0),
                rd: RegisterMapping::T0,
                opcode: u7::new(0b011_0011),
            }
        );
        Ok(())
    }
    #[test]
    fn test_andi() -> Result<()> {
        let machine_code: u32 = 0b0000_0000_1010_0110_0111_0110_1001_0011;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::IType {
                funct7: None,
                shamt: None,
                imm: i12::new(0xA),
                rs1: RegisterMapping::A2,
                funct3: u3::new(0b111),
                rd: RegisterMapping::A3,
                opcode: u7::new(0b001_0011),
            }
        );
        Ok(())
    }
    #[test]
    fn test_sb() -> Result<()> {
        let machine_code: u32 = 0b1111_1110_0011_0010_0000_1000_0010_0011;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::SType {
                imm: i12::new(-16),
                rs2: RegisterMapping::Gp,
                rs1: RegisterMapping::Tp,
                funct3: u3::new(0b000),
                opcode: u7::new(0b010_0011),
            }
        );
        Ok(())
    }
    #[test]
    fn test_bne() -> Result<()> {
        let machine_code: u32 = 0b0000_0001_1110_0010_1001_0011_0110_0011;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::SBType {
                imm: i13::new(6),
                rs2: RegisterMapping::T5,
                rs1: RegisterMapping::T0,
                funct3: u3::new(0b001),
                opcode: u7::new(0b110_0011),
            }
        );
        Ok(())
    }
    #[test]
    fn test_jal() -> Result<()> {
        let machine_code: u32 = 0b0000_0000_1010_0000_0000_0000_1110_1111;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::UJType {
                imm: u21::new(0xA), // 10
                rd: RegisterMapping::Ra,
                opcode: u7::new(0b110_1111),
            }
        );
        Ok(())
    }
    #[test]
    fn test_jal_2() -> Result<()> {
        let machine_code: u32 = 0b1000_0000_1011_0000_1000_0000_1110_1111;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::UJType {
                imm: u21::new(0b1_0000_1000_1000_0000_1010),
                rd: RegisterMapping::Ra,
                opcode: u7::new(0b110_1111),
            }
        );
        Ok(())
    }

    #[test]
    fn test_auipc() -> Result<()> {
        let machine_code: u32 = 0x0fc1_0497;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::UType {
                imm: u20::new(0x0fc10),
                rd: RegisterMapping::S1,
                opcode: u7::new(0b001_0111),
            }
        );
        Ok(())
    }

    #[test]
    fn test_lui() -> Result<()> {
        let machine_code: u32 = 0x186a_0337;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::UType {
                imm: u20::new(0x186a0),
                rd: RegisterMapping::T1,
                opcode: u7::new(0b011_0111),
            }
        );
        Ok(())
    }

    #[test]
    fn test_lw() -> Result<()> {
        let machine_code: u32 = 0x0043_A283;
        let instruction = Instruction::from_machine_code(machine_code)?;
        assert_eq!(
            instruction,
            Instruction::IType {
                funct7: None,
                shamt: None,
                imm: i12::new(4),
                rs1: RegisterMapping::T2,
                funct3: u3::new(0b010),
                rd: RegisterMapping::T0,
                opcode: u7::new(0b000_0011),
            }
        );
        Ok(())
    }
}
