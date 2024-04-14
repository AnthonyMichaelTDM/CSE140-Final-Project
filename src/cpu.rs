use anyhow::{bail, Result};
use ux::u3;

use crate::{
    alu::{alu, alu_control_unit},
    instruction::Instruction,
    registers::{RegisterFile, RegisterMapping},
    signals::{control_unit, ALUControl, ALUSrcA, ALUSrcB, BranchJump, ControlSignals, PCSrc},
    stages::{Immediate, EXMEM, IDEX, IF, IFID, MEMWB},
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

    pub fn get_instruction(&self, pc: u32) -> Option<u32> {
        if pc as usize / 4 >= self.rom.len() {
            // we've reached the end of the program
            return None;
        }
        if pc % 4 != 0 {
            panic!("PC not aligned to 4 bytes");
        }

        Some(self.rom[pc as usize / 4])
    }
}

/// an array that holds the data of the program.
/// Each data is a 32-bit integer.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct DataMemory {
    d_mem: [u32; 32],
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
    /// This variable will be updated by Execute() function and used by Fetch() function to decide the PC value of the next cycle.
    /// The branch_target variable will be set to the target address of the branch instruction.
    /// This will be used as the PC value in the next cycle if a branch was taken.
    branch_target: Option<u32>,
    /// This variable will be updated by Execute() function and used by Fetch() function to decide the PC value of the next cycle.
    /// The jump_target variable will be set to the target address of the jump instruction.
    /// This will be used as the PC value in the next cycle if a jump was taken.
    jump_target: Option<u32>,
    /// The PCSrc signal is a 2 bit signal that tells the cpu where to get the next PC value from.
    /// 00: PC + 4
    /// 01: branch_target
    /// 10: jump_target
    pc_src: PCSrc,
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
            branch_target: None,
            jump_target: None,
            total_clock_cycles: 0,
            control_signals: ControlSignals::default(),
            rf: RegisterFile::new(),
            d_mem: DataMemory::new(),
            i_mem: InstructionMemory::new(rom),
            pc_src: PCSrc::Next,
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
        loop {
            println!();
            match self.run_step() {
                Ok(report) => {
                    println!("{}", report);
                }
                Err(e) => {
                    eprintln!("Error: {}", e);
                    break;
                }
            }

            // if all the stage registers are flushed, we can stop the simulation
            todo!()
        }

        println!("program terminated:");
        println!("total execution time is {} cycles", self.total_clock_cycles);
    }

    /// Body of the main loop of the CPU simulator, separated for testing purposes
    pub fn run_step(&mut self) -> Result<Report> {
        let mut report = String::new();

        self.total_clock_cycles += 1;

        report.push_str(format!("total_clock_cycles {} :", self.total_clock_cycles).as_str());

        let ifid = self.fetch(IF {});
        let idex = self.decode(ifid)?;
        let exmem = self.execute(idex)?;
        let (memwb, mem_report) = self.mem(exmem);
        // mem will tell us if data memory was updated, so we add that to the report
        report.push_str(&mem_report);
        let wb_report = self.write_back(memwb);
        // wb will tell us if registers were updated, so we add those to the report
        report.push_str(&wb_report);

        Ok(report)
    }

    /// the Fetch stage of the CPU.
    fn fetch(&mut self, _if_reg: IF) -> IFID {
        // increment the program counter
        self.pc = match self.pc_src {
            PCSrc::Next => self.next_pc,
            PCSrc::BranchTarget => self.branch_target.unwrap(),
            PCSrc::JumpTarget => self.jump_target.unwrap(),
        };

        // get the current instruction from the ROM
        let instruction_code = self.i_mem.get_instruction(self.pc);

        self.next_pc = self.pc + 4;

        IFID { instruction_code }
    }

    /// the Decode stage of the CPU.
    fn decode(&mut self, ifid_reg: IFID) -> Result<IDEX> {
        // if the fetch stage failed, flush
        let Some(instruction) = ifid_reg.instruction_code else {
            return Ok(IDEX {
                instruction: Instruction::Flush,
                read_data_1: None,
                read_data_2: None,
                immediate: Immediate::None,
            });
        };

        // decode the instruction
        let instruction = Instruction::from_machine_code(instruction)?;

        // read the register file
        let read_data_1 = match instruction {
            Instruction::RType { rs1, .. }
            | Instruction::IType { rs1, .. }
            | Instruction::SType { rs1, .. }
            | Instruction::SBType { rs1, .. } => Some(self.rf.read(rs1)),
            Instruction::UType { .. } | Instruction::UJType { .. } => None,
            Instruction::Flush => unreachable!(),
        };
        let read_data_2 = match instruction {
            Instruction::RType { rs2, .. }
            | Instruction::SType { rs2, .. }
            | Instruction::SBType { rs2, .. } => Some(self.rf.read(rs2)),
            Instruction::IType { .. } | Instruction::UType { .. } | Instruction::UJType { .. }  => {
                None
            }
            Instruction::Flush => unreachable!(),
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
            Instruction::RType { .. } | Instruction::Flush => Immediate::None,
        };

        // set the control signals
        self.control_signals = control_unit(instruction.opcode().unwrap())?;

        Ok(IDEX {
            instruction,
            read_data_1,
            read_data_2,
            immediate,
        })
    }

    /// the Execute stage of the CPU.
    ///
    /// TODO: branch and jump address handling
    fn execute(&mut self, idex_reg: IDEX) -> Result<EXMEM> {
        // if the decode stage failed, flush
        if idex_reg.instruction == Instruction::Flush {
            return Ok(EXMEM {
                instruction: Instruction::Flush,
                alu_result: 0,
                alu_zero: false,
                read_data_2: None,
            });
        }


        // ALU control unit
        let alu_control = alu_control_unit(
            self.control_signals.alu_op,
            idex_reg.instruction.funct3(),
            idex_reg.instruction.funct7(),
        )?;

        // ALU operation
        let alu_operand_a: u32 = match self.control_signals.alu_src_a {
            ALUSrcA::Register => idex_reg.read_data_1.unwrap(), // TODO: data forwarding
            ALUSrcA::PC => self.pc,
            ALUSrcA::Constant0 => 0,
        };
        let alu_operand_b: u32 = match self.control_signals.alu_src_b {
            ALUSrcB::Register => idex_reg.read_data_2.unwrap(), // TODO: data forwarding
            ALUSrcB::Immediate => match idex_reg.immediate {
                Immediate::SignedImmediate(imm) => imm as u32,
                Immediate::AddressOffset(imm) => imm as u32,
                Immediate::BranchOffset(_) => {
                    bail!("branch offset should not be used as ALU operand")
                }
                Immediate::JumpOffset(imm) => imm as u32,
                Immediate::UpperImmediate(imm) => imm,
                Immediate::None => 0,
            },
            ALUSrcB::Constant4 => 4,
        };

        let (alu_zero, alu_result) = alu(alu_control, alu_operand_a, alu_operand_b);

        // signal used by the branch and jump unit to help it resolve the branch or jump instruction
        let operands_equal = alu_operand_a == alu_operand_b;

        // branch and jump address calculation
        match branching_jump_unit(
            self.control_signals.branch_jump,
            alu_zero,
            alu_control,
            operands_equal,
            idex_reg.instruction.funct3(),
        )? {
            PCSrc::BranchTarget => {
                let branch_offset = match idex_reg.immediate {
                    Immediate::BranchOffset(offset) => offset,
                    _ => return Err(anyhow::anyhow!("invalid immediate value")),
                };
                self.branch_target = Some(self.pc.wrapping_add_signed(branch_offset));
                self.pc_src = PCSrc::BranchTarget;
            }
            PCSrc::JumpTarget => {
                self.jump_target = Some(alu_result);
                self.pc_src = PCSrc::JumpTarget;
            }
            PCSrc::Next => {
                self.branch_target = None;
                self.jump_target = None;
                self.pc_src = PCSrc::Next;
            }
        }

        Ok(EXMEM {
            instruction: idex_reg.instruction,
            alu_result,
            alu_zero,
            read_data_2: idex_reg.read_data_2,
        })
    }

    /// the Memory stage of the CPU.
    fn mem(&mut self, exmem_reg: EXMEM) -> (MEMWB, String) {
        // if the execute stage failed, flush
        if exmem_reg.instruction == Instruction::Flush {
            return (MEMWB {
                instruction: Instruction::Flush,
                alu_result: 0,
                mem_read_data: None,
            }, String::new());
        }

        // Implement the Memory stage here

        match (self.control_signals.mem_read, self.control_signals.mem_write) {
            (true, false) => {
                // load
                let mem_read_data = self.d_mem.read(exmem_reg.alu_result);
                (MEMWB {
                    instruction: exmem_reg.instruction,
                    alu_result: exmem_reg.alu_result,
                    mem_read_data: Some(mem_read_data),
                },
                String::new()
                )
            }
            (false, true) => {
                // store
                self.d_mem.write(exmem_reg.alu_result, exmem_reg.read_data_2.expect("no data to store"));
                (MEMWB {
                    instruction: exmem_reg.instruction,
                    alu_result: exmem_reg.alu_result,
                    mem_read_data: None,
                },
                format!("memory 0x{:x} is modified to 0x{:x}",exmem_reg.alu_result,exmem_reg.read_data_2.expect("no data to store"))
                )
            }
            (false, false) => {
                // no memory operation
                (MEMWB {
                    instruction: exmem_reg.instruction,
                    alu_result: exmem_reg.alu_result,
                    mem_read_data: None,
                },String::new())
            }
            (true,true) => panic!("invalid control signals for memory stage"),
        }
    }

    /// the Write Back stage of the CPU.
    fn write_back(&mut self, memwb_reg: MEMWB) -> String {
        // if the memory stage failed, flush
        if memwb_reg.instruction == Instruction::Flush {
            return String::new();
        }

        match (self.control_signals.reg_write, memwb_reg.instruction.rd()) {
            (true, Some(rd)) => {
                // write to register file
                match self.control_signals.mem_to_reg {
                    true => {
                        // write the memory read data to the register file
                        self.rf.write(rd, memwb_reg.mem_read_data.expect("no data to write"));
                        format!("{rd} is modified to 0x{:x}",memwb_reg.mem_read_data.expect("no data to write"))
                    }
                    false => {
                        // write the ALU result to the register file
                        self.rf.write(rd, memwb_reg.alu_result);
                        format!("{rd} is modified to 0x{:x}",memwb_reg.alu_result)
                    }
                }
            }
            (true, None) => {
                // no write to register file
                String::new()
            }
            (false, _) => {
                // no write to register file
                String::new()
            }
        }
    }
}

/// The Branch and Jump Unit is responsible for determining whether a branch or jump should be taken.
///
/// # Arguments
///
/// * `branch_jump` - a 2 bit control signal that tells the Branching and Jump Unit what type of branching to consider.
/// * `alu_zero` - a signal that tells the Branching and Jump Unit whether the ALU result is zero.
/// * `alu_control` - the operation that the ALU performed.
/// * `operands_equal` - a signal that tells the Branching and Jump Unit whether the operands to the alu were are equal.
/// * `funct3` - the funct3 field of the instruction (only for branch instructions)
///
/// # Returns
///
/// * `Ok(None)` - if no branch or jump should be taken
/// * `Ok(Some((u32, PCSrc)))` - the target address and the source of the next PC value (which also determines where the returned target address should be stored)
/// * `Err(anyhow::Error)` - if the arguments are invalid or the operation is not supported
fn branching_jump_unit(
    branch_jump: BranchJump,
    alu_zero: bool,
    alu_control: ALUControl,
    operands_equal: bool,
    funct3: Option<u3>,
) -> Result<PCSrc> {
    match branch_jump {
        BranchJump::No => Ok(PCSrc::Next),
        BranchJump::Branch => {
            // branch instructions have a funct3 field
            let funct3 = u8::from(funct3.ok_or_else(|| {
                anyhow::anyhow!("funct3 field is required for branch instructions")
            })?);

            // first, we need to check the type of branch instruction being done, we can use the ALU Control Signal to determine this
            // then we do some logic based on the func3 field of the instruction
            match (alu_control, funct3, alu_zero, operands_equal) {
                // take branch:
                (
                    // beq
                    ALUControl::SUB,
                    0b000,
                    true,
                    true,
                )
                | // bne
                (
                    ALUControl::SUB,
                    0b001,
                    false,
                    false,
                )
                | (
                    // blt
                    ALUControl::SLT,
                    0b100,
                    true,
                    false,
                )
                | (
                    // bge
                    ALUControl::SLT,
                    0b101,
                    false,
                    _,
                )
                | (
                    // bltu
                    ALUControl::SLTU,
                    0b110,
                    true,
                    false,
                )
                | (
                    // bgeu
                    ALUControl::SLTU,
                    0b111,
                    false,
                    _,
                ) => Ok(PCSrc::BranchTarget),

                // don't take branch
                (
                    // beq
                    ALUControl::SUB,
                    0b000,
                    false,
                    false,
                )
                | // bne
                (  
                    ALUControl::SUB,
                    0b001,
                    true,
                    true,
                )
                | (
                    // blt
                    ALUControl::SLT,
                    0b100,
                    false,
                    _,
                )
                | (
                    // bge
                    ALUControl::SLT,
                    0b101,
                    true,
                    true,
                )
                | (
                    // bltu
                    ALUControl::SLTU,
                    0b110,
                    false,
                    _,
                )
                | (
                    // bgeu
                    ALUControl::SLTU,
                    0b111,
                    true,
                    true,
                ) => Ok(PCSrc::Next),

                _ => bail!("invalid branch instruction"),
            }
        }
        BranchJump::Jump => Ok(PCSrc::JumpTarget),
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ux::{i12, u3, u7};

    use super::*;
    use crate::instruction::Instruction;

    #[test]
    fn test_cpu_new() {
        let rom = vec![0; 32];
        let cpu = CPU::new(rom);

        assert_eq!(cpu.pc, 0);
        assert_eq!(cpu.next_pc, 0);
        assert_eq!(cpu.branch_target, None);
        assert_eq!(cpu.jump_target, None);
        assert_eq!(cpu.total_clock_cycles, 0);
        assert_eq!(cpu.control_signals, ControlSignals::default());
        assert_eq!(cpu.rf, RegisterFile::new());
        assert_eq!(cpu.d_mem, DataMemory::new());
        assert_eq!(cpu.i_mem.rom, vec![0; 32]);
    }

    #[test]
    fn test_cpu_initialize_rf() {
        let rom = vec![0; 32];
        let mut cpu = CPU::new(rom);

        let mappings = &[
            (RegisterMapping::Ra, 1),
            (RegisterMapping::Sp, 2),
            (RegisterMapping::Gp, 3),
            (RegisterMapping::Tp, 4),
            (RegisterMapping::T0, 5),
            (RegisterMapping::T1, 6),
            (RegisterMapping::T2, 7),
            (RegisterMapping::S0, 8),
            (RegisterMapping::S1, 9),
            (RegisterMapping::A0, 10),
            (RegisterMapping::A1, 11),
            (RegisterMapping::A2, 12),
            (RegisterMapping::A3, 13),
            (RegisterMapping::A4, 14),
            (RegisterMapping::A5, 15),
            (RegisterMapping::A6, 16),
            (RegisterMapping::A7, 17),
            (RegisterMapping::S2, 18),
            (RegisterMapping::S3, 19),
            (RegisterMapping::S4, 20),
            (RegisterMapping::S5, 21),
            (RegisterMapping::S6, 22),
            (RegisterMapping::S7, 23),
            (RegisterMapping::S8, 24),
            (RegisterMapping::S9, 25),
            (RegisterMapping::S10, 26),
            (RegisterMapping::S11, 27),
            (RegisterMapping::T3, 28),
            (RegisterMapping::T4, 29),
            (RegisterMapping::T5, 30),
            (RegisterMapping::T6, 31),
        ];

        cpu.initialize_rf(mappings);

        for (mapping, value) in mappings {
            assert_eq!(cpu.rf.read(*mapping), *value);
        }
    }

    #[test]
    fn test_cpu_fetch() {
        let rom = vec![0x00000013, 0x00000093, 0x00000073, 0x00000033];
        let mut cpu = CPU::new(rom);

        let ifid = cpu.fetch(IF {});

        assert_eq!(ifid.instruction_code.unwrap(), 0x00000013);
        assert_eq!(cpu.pc, 0);
        assert_eq!(cpu.next_pc, 4);

        let ifid = cpu.fetch(IF {});

        assert_eq!(ifid.instruction_code.unwrap(), 0x00000093);
        assert_eq!(cpu.pc, 4);
        assert_eq!(cpu.next_pc, 8);

        let ifid = cpu.fetch(IF {});

        assert_eq!(ifid.instruction_code.unwrap(), 0x00000073);
        assert_eq!(cpu.pc, 8);
        assert_eq!(cpu.next_pc, 12);

        let ifid = cpu.fetch(IF {});

        assert_eq!(ifid.instruction_code.unwrap(), 0x00000033);
        assert_eq!(cpu.pc, 12);
        assert_eq!(cpu.next_pc, 16);
    }

    #[test]
    fn test_cpu_decode() {
        let rom = vec![0x00000013];
        let mut cpu = CPU::new(rom);

        let ifid = cpu.fetch(IF {});
        let idex = cpu.decode(ifid).unwrap();

        assert_eq!(
            idex.instruction,
            Instruction::IType {
                funct7: None,
                shamt: None,
                opcode: u7::new(0b0010011),
                rd: RegisterMapping::Zero,
                funct3: u3::new(0),
                rs1: RegisterMapping::Zero,
                imm: i12::new(0),
            }
        );
        assert_eq!(idex.read_data_1, Some(0));
        assert_eq!(idex.read_data_2, None);
        assert_eq!(idex.immediate, Immediate::SignedImmediate(0));
    }

    #[test]
    fn test_cpu_execute() {
        let rom = vec![0x00000013];
        let mut cpu = CPU::new(rom);

        let ifid = cpu.fetch(IF {});
        let idex = cpu.decode(ifid).unwrap();
        let exmem = cpu.execute(idex).unwrap();

        assert_eq!(
            exmem.instruction,
            Instruction::IType {
                funct7: None,
                shamt: None,
                opcode: u7::new(0b0010011),
                rd: RegisterMapping::Zero,
                funct3: u3::new(0),
                rs1: RegisterMapping::Zero,
                imm: i12::new(0),
            }
        );
        assert_eq!(exmem.alu_result, 0);
        assert_eq!(exmem.alu_zero, true);
        assert_eq!(exmem.read_data_2, None);
    }

    #[test]
    fn test_cpu_mem() {
        // this instruction will load the value at offset 4 from the address in register T2 into register T0
        let rom = vec![0x0043_A283];
        let mut cpu = CPU::new(rom);

        // put some data in the data memory
        cpu.d_mem.write(0, 5);
        cpu.d_mem.write(4, 10);
        cpu.d_mem.write(8, 15);

        let ifid = cpu.fetch(IF {});
        let idex = cpu.decode(ifid).unwrap();
        let exmem = cpu.execute(idex).unwrap();
        let (memwb, _) = cpu.mem(exmem);

        assert_eq!(memwb.mem_read_data, Some(10));
    }

    #[test]
    fn test_cpu_write_back() {
        let rom = vec![0b0000_0000_1010_0110_0111_0110_1001_0011];
        let mut cpu = CPU::new(rom);

        let ifid = cpu.fetch(IF {});
        let idex = cpu.decode(ifid).unwrap();
        let exmem = cpu.execute(idex).unwrap();
        let (memwb, _) = cpu.mem(exmem);
        cpu.write_back(memwb);

        assert_eq!(cpu.rf.read(RegisterMapping::A3), 10);
    }
}
