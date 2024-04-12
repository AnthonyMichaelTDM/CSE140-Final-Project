use ux::{u1, u2, u4};

use crate::registers::{RegisterFile, RegisterMapping};

/// an array that holds the instructions of the program.
/// Each instruction is a 32-bit integer.
/// The program counter (PC) will be used to index this array to get the current instruction.
/// The PC will be updated by the Fetch() function to get the next instruction in the next cycle.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ROM {
    rom: Vec<u32>,
}

impl ROM {
    pub fn new(rom: Vec<u32>) -> Self {
        Self { rom }
    }

    pub fn get_instruction(&self, pc: u32) -> u32 {
        if pc as usize / 4 >= self.rom.len() {
            panic!("PC out of bounds");
        }
        if pc % 4 != 0 {
            panic!("PC not aligned to 4 bytes");
        }

        self.rom[pc as usize / 4]
    }
}

/// an array that holds the data of the program.
/// Each data is a 32-bit integer.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct DataMemory {
    pub d_mem: [u32; 32],
}

impl DataMemory {
    pub fn new() -> Self {
        Self { d_mem: [0; 32] }
    }

    pub fn read(&self, address: u32) -> u32 {
        if address as usize / 4 >= self.d_mem.len() {
            panic!("Address out of bounds");
        }
        if address % 4 != 0 {
            panic!("Address not aligned to 4 bytes");
        }

        self.d_mem[address as usize / 4]
    }

    pub fn write(&mut self, address: u32, value: u32) {
        if address as usize / 4 >= self.d_mem.len() {
            panic!("Address out of bounds");
        }
        if address % 4 != 0 {
            panic!("Address not aligned to 4 bytes");
        }

        self.d_mem[address as usize / 4] = value;
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct ControlSignals {
    /// tells the register file to write to the register specified by the instruction.
    pub reg_write: Option<bool>,
    /// The branch signal is a 1 bit signal that controls whether a branch *can* be taken. (It is not the branch condition itself. That is determined by the ALU zero signal.)
    pub branch: Option<bool>,
    /// The ALUSrc signal is a 1 bit signal that tells the ALU whether to use the register value (0) or the immediate value (1) as the second operand.
    pub alu_src: Option<u1>,
    /// The ALU operation signal is a 2 bit signal that tells the ALU Control Unit what type of instruction is being executed.
    pub alu_op: Option<u2>,
    /// The mem_write signal is a 1 bit signal that tells the data memory unit whether to write to memory.
    pub mem_write: Option<bool>,
    /// controls whether the write back stages uses the output of the data memory unit or the ALU.
    pub mem_to_reg: Option<bool>,
    /// The mem_read signal is a 1 bit signal that tells the data memory unit whether to read from memory.
    pub mem_read: Option<bool>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CPU {
    pc: u32,
    next_pc: u32,
    /// This variable will be updated by Execute() function and used when deciding to use branch target address in the next cycle.
    /// The zero variable will be set to 1 by ALU when the computation result is zero and unset to 0 if otherwise.
    alu_zero: bool,
    alu_ctrl: u4,
    /// This variable will be updated by Execute() function and used by Fetch() function to decide the PC value of the next cycle.
    branch_target: u32,
    total_clock_cycles: u64,
    control_signals: ControlSignals,
    /// an integer array that has 32 entries.
    /// This register file array will be initialized to have all zeros unless otherwise specified.
    /// This register file will be updated by WriteBack() function.
    /// This register file can be indexed by with `RegisterMapping` enum variants for ergonomics.
    rf: RegisterFile,
    /// an integer array that has 32 entries.
    /// Each entry of this array will be considered as one 4-byte memory space.
    /// We assume that the data memory address begins from `0x0`.
    /// Therefore, each entry of the `d_mem` array will be accessed with the following addresses.
    ///
    /// | Memory address calculated at Execute() | Entry to access in `d_mem` array |
    /// |----------------------------------------|----------------------------------|
    /// |               `0x00000000`             |             `d_mem[0]`           |
    /// |               `0x00000004`             |             `d_mem[1]`           |
    /// |               `0x00000008`             |             `d_mem[2]`           |
    /// |                    …                   |                  …               |
    /// |               `0x0000007C`             |             `d_mem[31]`          |
    d_mem: DataMemory,
    /// an array that holds the instructions of the program.
    /// Each instruction is a 32-bit integer.
    /// The program counter (PC) will be used to index this array to get the current instruction.
    /// The PC will be updated by the Fetch() function to get the next instruction in the next cycle.
    rom: ROM,
}

impl CPU {
    /// Initialize the CPU state
    pub fn new(rom: Vec<u32>) -> Self {
        Self {
            pc: 0,
            next_pc: 0,
            alu_zero: false,
            alu_ctrl: u4::new(0),
            branch_target: 0,
            total_clock_cycles: 0,
            control_signals: ControlSignals::default(),
            rf: RegisterFile::new(),
            d_mem: DataMemory::new(),
            rom: ROM::new(rom),
        }
    }

    pub fn initialize_rf(&mut self, mappings: &[(RegisterMapping, u32)]) {
        self.rf.initialize(mappings);
    }

    pub fn get_total_clock_cycles(&self) -> u64 {
        self.total_clock_cycles
    }

    /// Main loop of the CPU simulator
    pub fn run(&mut self) {}

    /// Body of the main loop of the CPU simulator, separated for testing purposes
    pub fn run_step(&mut self) {}

    fn fetch(&mut self) {
        // Implement the Fetch stage here
    }

    fn decode(&mut self) {
        // Implement the Decode stage here
    }

    fn execute(&mut self) {
        // Implement the Execute stage here
    }

    fn mem(&mut self) {
        // Implement the Memory stage here
    }

    fn write_back(&mut self) {
        // Implement the Write Back stage here
    }
}
