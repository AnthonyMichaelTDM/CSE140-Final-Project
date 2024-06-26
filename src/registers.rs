use std::{
    fmt,
    ops::{Index, IndexMut},
};

use anyhow::bail;

/// the number of registers in the RISC-V ISA
pub const REGISTERS_COUNT: u8 = 32;

/// This enum represents the mapping of the registers to their indices in the register file.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum RegisterMapping {
    Zero = 0,
    Ra = 1,
    Sp = 2,
    Gp = 3,
    Tp = 4,
    T0 = 5,
    T1 = 6,
    T2 = 7,
    S0 = 8,
    S1 = 9,
    A0 = 10,
    A1 = 11,
    A2 = 12,
    A3 = 13,
    A4 = 14,
    A5 = 15,
    A6 = 16,
    A7 = 17,
    S2 = 18,
    S3 = 19,
    S4 = 20,
    S5 = 21,
    S6 = 22,
    S7 = 23,
    S8 = 24,
    S9 = 25,
    S10 = 26,
    S11 = 27,
    T3 = 28,
    T4 = 29,
    T5 = 30,
    T6 = 31,
}

impl fmt::Display for RegisterMapping {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", *self as u8)
    }
}

impl TryFrom<u8> for RegisterMapping {
    type Error = anyhow::Error;
    fn try_from(value: u8) -> Result<Self, anyhow::Error> {
        if value >= REGISTERS_COUNT {
            bail!(
                "Invalid register number provided to RegisterMapping::from(u8): {}",
                value
            );
        }
        // this is safe because:
        // 1. the value is checked to be within the range of the enum
        // 2. the enum is repr(u8), so the memory layout is the same as u8
        // 3. we explicityly define the src and dst generics to ensure that future changes to the enum's memory size are caught at compile time
        Ok(unsafe { std::mem::transmute::<u8, Self>(value) })
    }
}

/// a struct that represents the register file of the CPU.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct RegisterFile {
    registers: [u32; REGISTERS_COUNT as usize],
}

impl Index<RegisterMapping> for RegisterFile {
    type Output = u32;
    fn index(&self, index: RegisterMapping) -> &Self::Output {
        &self.registers[index as usize]
    }
}

impl IndexMut<RegisterMapping> for RegisterFile {
    fn index_mut(&mut self, index: RegisterMapping) -> &mut Self::Output {
        assert!(
            index != RegisterMapping::Zero,
            "Cannot write to the zero register"
        );
        &mut self.registers[index as usize]
    }
}

impl RegisterFile {
    /// Create a new `RegisterFile` with all registers initialized to 0
    #[must_use]
    pub const fn new() -> Self {
        Self {
            registers: [0; REGISTERS_COUNT as usize],
        }
    }

    /// Initialize the register file with the provided defaults, makes everything else 0
    ///
    /// # Arguments
    ///
    /// * `mappings` - a list of tuples where the first element is the register to write to and the second element is the value to write
    ///
    /// # Panics
    ///
    /// Panics if the register to write to is `RegisterMapping::Zero`
    pub fn initialize(&mut self, mappings: &[(RegisterMapping, u32)]) {
        self.registers = [0; REGISTERS_COUNT as usize];
        for (mapping, value) in mappings {
            self[*mapping] = *value;
        }
    }

    /// Read the value of a register
    ///
    /// # Arguments
    ///
    /// * `reg` - the register to read from
    ///
    /// # Returns
    ///
    /// The value of the register
    #[must_use]
    pub const fn read(&self, reg: RegisterMapping) -> u32 {
        self.registers[reg as usize]
    }

    /// Write a value to a register
    ///
    /// # Arguments
    ///
    /// * `reg` - the register to write to
    /// * `value` - the value to write
    pub fn write(&mut self, reg: RegisterMapping, value: u32) {
        self.registers[reg as usize] = value;
    }
}
