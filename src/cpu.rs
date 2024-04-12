use anyhow::Result;
use ux::u4;

use crate::{
    instruction::Instruction,
    registers::{RegisterFile, RegisterMapping},
    signals::{control_unit, ControlSignals, PCSrc},
    stages::{Immediate, EXMEM, IDEX, IF, IFID, MEMWB, WB},
};

/// a string that holds a report of what happened in the CPU during a clock cycle.
pub type Report = String;

/// an array that holds the instructions of the program.
/// Each instruction is a 32-bit integer.
/// The program counter (PC) will be used to index this array to get the current instruction.
/// The PC will be updated by the Fetch() function to get the next instruction in the next cycle.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InstructionMemory {
    rom: Vec<u32>,
}

impl InstructionMemory {
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CPU {
    pc: u32,
    /// This variable will be updated by Fetch() function and used as the PC value in the next cycle if no branch or jump was taken.
    next_pc: u32,
    /// This variable will be updated by Execute() function and used when deciding to use branch target address in the next cycle.
    /// The zero variable will be set to 1 by ALU when the computation result is zero and unset to 0 if otherwise.
    alu_zero: bool,
    alu_ctrl: u4,
    /// This variable will be updated by Execute() function and used by Fetch() function to decide the PC value of the next cycle.
    /// The branch_target variable will be set to the target address of the branch instruction.
    /// This will be used as the PC value in the next cycle if a branch was taken.
    branch_target: u32,
    /// This variable will be updated by Execute() function and used by Fetch() function to decide the PC value of the next cycle.
    /// The jump_target variable will be set to the target address of the jump instruction.
    /// This will be used as the PC value in the next cycle if a jump was taken.
    jump_target: u32,
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
    i_mem: InstructionMemory,
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
            jump_target: 0,
            total_clock_cycles: 0,
            control_signals: ControlSignals::default(),
            rf: RegisterFile::new(),
            d_mem: DataMemory::new(),
            i_mem: InstructionMemory::new(rom),
        }
    }

    pub fn initialize_rf(&mut self, mappings: &[(RegisterMapping, u32)]) {
        self.rf.initialize(mappings);
    }

    pub fn get_total_clock_cycles(&self) -> u64 {
        self.total_clock_cycles
    }

    /// Main loop of the CPU simulator
    pub fn run(&mut self) {
        todo!()
    }

    /// Body of the main loop of the CPU simulator, separated for testing purposes
    pub fn run_step(&mut self) -> Result<Report> {
        let mut report = String::new();

        self.total_clock_cycles += 1;

        report.push_str(format!("total_clock_cycles {} :", self.total_clock_cycles).as_str());

        let ifid = self.fetch(IF {});
        let idex = self.decode(ifid)?;
        let exmem = self.execute(idex);
        let memwb = self.mem(exmem);
        let _wb = self.write_back(memwb);

        // if wb will tell us what datamemory / registers were updated, so we add those to the report

        todo!()
    }

    /// the Fetch stage of the CPU.
    fn fetch(&mut self, _if_reg: IF) -> IFID {
        // increment the program counter
        self.pc = match self.control_signals.pc_src {
            PCSrc::Next => self.next_pc,
            PCSrc::BranchTarget => self.branch_target,
            PCSrc::JumpTarget => self.jump_target,
        };

        // get the current instruction from the ROM
        let instruction_code = self.i_mem.get_instruction(self.pc);

        self.next_pc = self.pc + 4;

        IFID { instruction_code }
    }

    /// the Decode stage of the CPU.
    fn decode(&mut self, ifid_reg: IFID) -> Result<IDEX> {
        // Implement the Decode stage here
        let instruction = Instruction::from_machine_code(ifid_reg.instruction_code)?;

        // read the register file
        let read_data_1 = match instruction {
            Instruction::RType { rs1, .. }
            | Instruction::IType { rs1, .. }
            | Instruction::SType { rs1, .. }
            | Instruction::SBType { rs1, .. } => Some(self.rf.read(rs1)),
            Instruction::UType { .. } | Instruction::UJType { .. } => None,
        };
        let read_data_2 = match instruction {
            Instruction::RType { rs2, .. }
            | Instruction::SType { rs2, .. }
            | Instruction::SBType { rs2, .. } => Some(self.rf.read(rs2)),
            Instruction::IType { .. } | Instruction::UType { .. } | Instruction::UJType { .. } => {
                None
            }
        };

        // sign extend the immediate value
        let immediate = match instruction {
            Instruction::IType { imm, .. } => {
                Immediate::SignedImmediate(i32::from(imm) << (32 - 12) >> (32 - 12))
            }
            Instruction::SType { imm, .. } => {
                Immediate::AddressOffset(i32::from(imm) << (32 - 12) >> (32 - 12))
            }
            Instruction::SBType { imm, .. } => {
                Immediate::BranchOffset(i32::from(imm) << (32 - 13) >> (32 - 13))
            }
            Instruction::UType { imm, .. } => {
                Immediate::UpperImmediate(u32::from(imm) << (32 - 20))
            }
            Instruction::UJType { imm, .. } => {
                Immediate::JumpOffset((u32::from(imm) as i32) << (32 - 21) >> (32 - 21))
            }
            Instruction::RType { .. } => Immediate::None,
        };

        // set the control signals
        self.control_signals = control_unit(instruction.opcode());

        Ok(IDEX {
            instruction,
            read_data_1,
            read_data_2,
            immediate,
        })
    }

    fn execute(&mut self, idex_reg: IDEX) -> EXMEM {
        // Implement the Execute stage here
        todo!()
    }

    fn mem(&mut self, exmem_reg: EXMEM) -> MEMWB {
        // Implement the Memory stage here
        todo!()
    }

    fn write_back(&mut self, memwb_reg: MEMWB) -> WB {
        // Implement the Write Back stage here
        todo!()
    }
}
