use anyhow::{bail, Result};
use ux::u3;

use crate::{
    alu::{alu, alu_control_unit},
    hazard_detection::{forwarding_unit, ForwardA, ForwardB, HazardDetectionUnit},
    instruction::Instruction,
    registers::{RegisterFile, RegisterMapping},
    signals::{control_unit, ALUControl, ALUSrcA, ALUSrcB, BranchJump, PCSrc},
    stages::{ExMem, IdEx, IfId, Immediate, MemWb, StageRegisters, Wb},
};

/// a string that holds a report of what happened in the CPU during a clock cycle.
pub type Report = String;

/// an array that holds the instructions of the program.
/// Each instruction is a 32-bit integer.
/// The program counter (PC) will be used to index this array to get the current instruction.
/// The PC will be updated by the `Fetch()` function to get the next instruction in the next cycle.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InstructionMemory {
    rom: Vec<u32>,
}

impl InstructionMemory {
    /// create a new `InstructionMemory` instance.
    ///
    /// # Arguments
    ///
    /// * `rom` - the program instructions
    ///
    /// # Returns
    ///
    /// a new `InstructionMemory` instance
    #[must_use]
    pub fn new(rom: Vec<u32>) -> Self {
        Self { rom }
    }

    /// get the instruction at the given program counter value.
    ///
    /// # Panics
    ///
    /// * if the program counter value is not aligned to 4 bytes
    ///
    /// # Arguments
    ///
    /// * `pc` - the program counter value
    ///
    /// # Returns
    ///
    /// * `Some(u32)` - the instruction at the given program counter value
    #[must_use]
    pub fn get_instruction(&self, pc: u32) -> Option<u32> {
        if pc as usize / 4 >= self.rom.len() {
            // we've reached the end of the program
            return None;
        }
        // check invariant
        assert!(pc % 4 == 0, "PC not aligned to 4 bytes");

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
    /// create a new `DataMemory` instance.
    ///
    /// # Returns
    ///
    /// a new `DataMemory` instance, initialized with all zeros
    #[must_use]
    pub const fn new() -> Self {
        Self { d_mem: [0; 32] }
    }

    /// read a 32-bit value from the data memory
    ///
    /// # Panics
    ///
    /// * if the address is out of bounds or not aligned to 4 bytes
    ///
    /// # Arguments
    ///
    /// * `address` - the address to read from
    ///
    /// # Returns
    ///
    /// the 32-bit value at the address
    #[must_use]
    pub fn read(&self, address: u32) -> u32 {
        // check invariants first
        assert!(
            address as usize / 4 < self.d_mem.len(),
            "Address out of bounds"
        );
        assert!(address % 4 == 0, "Address not aligned to 4 bytes");

        self.d_mem[address as usize / 4]
    }

    /// write a 32-bit value to the data memory
    ///
    /// # Panics
    ///
    /// * if the address is out of bounds or not aligned to 4 bytes
    ///
    /// # Arguments
    ///
    /// * `address` - the address to write to
    /// * `value` - the value to write
    pub fn write(&mut self, address: u32, value: u32) {
        // check invariants first
        assert!(
            address as usize / 4 < self.d_mem.len(),
            "Address out of bounds"
        );
        assert!(address % 4 == 0, "Address not aligned to 4 bytes");

        self.d_mem[address as usize / 4] = value;
    }
}

/// a struct that represents the CPU.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CPU {
    /// the program counter value of the current instruction.
    pc: u32,
    /// the next program counter value.
    pc_src: PCSrc,
    /// signal that, when flipped, flushes the IF stage (prevents it from running for a cycle)
    /// this is used to indicate stalls in the pipeline
    if_flush: bool,
    /// the total number of clock cycles that the CPU has executed.
    total_clock_cycles: u64,
    /// the stage registers of the CPU.
    /// These registers will be updated by the corresponding stage functions.
    stage_registers: StageRegisters,
    /// an integer array that has 32 entries.
    /// This register file array will be initialized to have all zeros unless otherwise specified.
    /// This register file will be updated by `write_back()` function.
    /// This register file can be indexed by with `RegisterMapping` enum variants for ergonomics.
    rf: RegisterFile,
    /// an integer array that has 32 entries.
    /// Each entry of this array will be considered as one 4-byte memory space.
    /// We assume that the data memory address begins from `0x0`.
    /// Therefore, each entry of the `d_mem` array will be accessed with the following addresses.
    ///
    /// | Memory address | Entry to access |
    /// |                | in `d_mem` array|
    /// |----------------|-----------------|
    /// |  `0x00000000`  |`d_mem[0]`       |
    /// |  `0x00000004`  |`d_mem[1]`       |
    /// |  `0x00000008`  |`d_mem[2]`       |
    /// |       …        |     …           |
    /// |  `0x0000007C`  |`d_mem[31]`      |
    d_mem: DataMemory,
    /// an array that holds the instructions of the program.
    /// Each instruction is a 32-bit integer.
    /// The program counter (PC) will be used to index this array to get the current instruction.
    /// The PC will be updated by the `fetch()` function to get the next instruction in the next cycle.
    i_mem: InstructionMemory,
}

impl CPU {
    /// Initialize the CPU state
    ///
    /// # Arguments
    ///
    /// * `rom` - the program instructions
    ///
    /// # Returns
    ///
    /// a new `CPU` instance
    #[must_use]
    pub fn new(rom: Vec<u32>) -> Self {
        Self {
            pc: 0,
            pc_src: PCSrc::Init,
            if_flush: false,
            total_clock_cycles: 0,
            stage_registers: StageRegisters::default(),
            rf: RegisterFile::new(),
            d_mem: DataMemory::new(),
            i_mem: InstructionMemory::new(rom),
        }
    }

    /// Initialize the register file with the given mappings
    ///
    /// exposes the `initialize` method of the `RegisterFile` struct
    pub fn initialize_rf(&mut self, mappings: &[(RegisterMapping, u32)]) {
        self.rf.initialize(mappings);
    }

    /// Initialize the data memory with the given data
    ///
    /// # Arguments
    ///
    /// * `data` - a list of tuples where the first element is the address to write to and the second element is the value to write
    pub fn initialize_dmem(&mut self, data: &[(u32, u32)]) {
        for (address, value) in data {
            self.d_mem.write(*address, *value);
        }
    }

    /// # Returns
    ///
    /// the total number of clock cycles that the CPU has executed
    #[must_use]
    pub const fn get_total_clock_cycles(&self) -> u64 {
        self.total_clock_cycles
    }

    /// is the program over
    ///
    /// # Returns
    ///
    /// `true` if the program is over, `false` otherwise
    #[must_use]
    pub fn is_done(&self) -> bool {
        self.pc_src == PCSrc::End
            && matches!(self.stage_registers.ifid, IfId::Flush)
            && matches!(self.stage_registers.idex, IdEx::Flush)
            && matches!(self.stage_registers.exmem, ExMem::Flush)
            && matches!(self.stage_registers.memwb, MemWb::Flush)
    }

    /// Main loop of the CPU simulator
    ///
    /// This function will run the CPU until the program is over
    ///
    /// It will print the report of each clock cycle
    pub fn run(&mut self) {
        loop {
            println!();
            match self.run_step() {
                Ok(report) => {
                    println!("{report}");
                }
                Err(e) => {
                    eprintln!("Error: {e}");
                    break;
                }
            }

            if self.is_done() {
                break;
            }
        }

        println!("program terminated:");
        println!("total execution time is {} cycles", self.total_clock_cycles);
    }

    /// Body of the main loop of the CPU simulator, separated for testing purposes
    ///
    /// This function will run the CPU for one clock cycle
    ///
    /// Pipeline stages are executed in reverse order to simplify the implementation
    ///
    /// # Returns
    ///
    /// * `Ok(Report)` - a report of what happened in the CPU during a clock cycle
    ///
    /// # Errors
    ///
    /// * if there is an error in the CPU pipeline
    pub fn run_step(&mut self) -> Result<Report> {
        let mut report = String::new();

        self.total_clock_cycles += 1;

        report.push_str(format!("total_clock_cycles {} :\n", self.total_clock_cycles).as_str());

        let wb_report = self.write_back();
        let mem_report = self.mem();
        self.execute()?;
        self.decode()?;
        let if_report = self.fetch();

        // mem will tell us if data memory was updated, so we add that to the report
        report.push_str(&mem_report);
        // wb will tell us if registers were updated, so we add those to the report
        report.push_str(&wb_report);
        // if will tell us if the pc was updated, so we add that to the report
        report.push_str(&if_report);

        Ok(report)
    }

    /// the Fetch stage of the CPU.
    ///
    /// # Returns
    ///
    /// a report of what happened in the CPU during the fetch stage
    fn fetch(&mut self) -> String {
        // check if the decode stage indicates a stall
        if self.stage_registers.idex == IdEx::Stall {
            // in this case, we don't need to do anything in the fetch stage
            return String::from("pipeline stalled in the decode stage\n");
        }

        // if the execute stage told us to flush the IF stage, we don't need to do anything
        if self.if_flush {
            self.if_flush = false;
            return String::from("pipeline flushed\n");
        }

        // increment the program counter
        self.pc = self.pc_src.next(self.pc);
        // get the current instruction from the ROM
        let Some(instruction_code) = self.i_mem.get_instruction(self.pc) else {
            // flush IFID and set pc to PCSrc::END if the program is over
            self.pc_src = PCSrc::End;
            self.stage_registers.ifid = IfId::Flush;
            return String::new();
        };
        // set the IF/ID stage registers
        self.stage_registers.ifid = IfId::If {
            instruction_code,
            pc: self.pc,
        };

        // report if the pc was modified
        let report: String = match self.pc_src {
            PCSrc::Init => String::new(),
            PCSrc::End => {
                return String::new();
            }
            _ => format!("pc is modified to 0x{:x}\n", self.pc),
        };
        // if the pc_src was init, branch, or jump, we need to reset it to next
        if matches!(
            self.pc_src,
            PCSrc::Init | PCSrc::BranchTarget { .. } | PCSrc::JumpTarget { .. }
        ) {
            self.pc_src = PCSrc::Next;
        }

        report
    }

    /// the Decode stage of the CPU.
    ///
    /// This function will decode the instruction in the IF/ID stage and set the ID/EX stage registers.
    ///
    /// # Errors
    ///
    /// * if the instruction in the IF/ID stage is invalid
    fn decode(&mut self) -> Result<()> {
        // if the fetch stage failed, flush and exit early
        let (instruction_code, pc) = match self.stage_registers.ifid {
            IfId::Flush => {
                self.stage_registers.idex = IdEx::Flush;
                return Ok(());
            }
            IfId::If {
                instruction_code,
                pc,
            } => (instruction_code, pc),
        };

        // decode the instruction
        let instruction = Instruction::from_machine_code(instruction_code)?;

        // check for a load-use hazard
        if HazardDetectionUnit::prime(instruction, self.stage_registers.idex)
            .detect_stall_conditions()
        {
            self.stage_registers.idex = IdEx::Stall;
            return Ok(());
        }

        // read the register file
        let (rs1, read_data_1) = match instruction {
            Instruction::RType { rs1, .. }
            | Instruction::IType { rs1, .. }
            | Instruction::SType { rs1, .. }
            | Instruction::SBType { rs1, .. } => (Some(rs1), Some(self.rf.read(rs1))),
            Instruction::UType { .. } | Instruction::UJType { .. } => (None, None),
        };
        let (rs2, read_data_2) = match instruction {
            Instruction::RType { rs2, .. }
            | Instruction::SType { rs2, .. }
            | Instruction::SBType { rs2, .. } => (Some(rs2), Some(self.rf.read(rs2))),
            Instruction::IType { .. } | Instruction::UType { .. } | Instruction::UJType { .. } => {
                (None, None)
            }
        };

        // sign extend the immediate value
        let immediate: Immediate = match instruction {
            Instruction::IType { imm, .. } | Instruction::SType { imm, .. } => {
                Immediate::SignedImmediate(i32::from(imm) << (32 - 12) >> (32 - 12))
            }
            Instruction::SBType { imm, .. } => {
                Immediate::BranchOffset(i32::from(imm) << (32 - 13) >> (32 - 13))
            }
            Instruction::UType { imm, .. } => {
                Immediate::UpperImmediate(u32::from(imm) << (32 - 20))
            }
            Instruction::UJType { imm, .. } =>
            {
                #[allow(clippy::cast_possible_wrap)]
                Immediate::JumpOffset((u32::from(imm) as i32) << (32 - 21) >> (32 - 21))
            }
            Instruction::RType { .. } => Immediate::None,
        };

        // set the control signals
        let control_signals = control_unit(instruction.opcode())?;

        // set the ID/EX stage registers
        self.stage_registers.idex = IdEx::Id {
            instruction,
            rs1,
            read_data_1,
            rs2,
            read_data_2,
            immediate,
            pc,
            control_signals,
        };

        Ok(())
    }

    /// the Execute stage of the CPU.
    ///
    /// This function will execute the instruction in the ID/EX stage and set the EX/MEM stage registers.
    ///
    /// # Errors
    ///
    /// * if the ALU control unit fails
    /// * if the branch and jump unit fails
    /// * if an invalid immediate value is found
    fn execute(&mut self) -> Result<()> {
        // if the decode stage failed, flush and exit early
        let (instruction, read_data_1, read_data_2, immediate, pc, control_signals) =
            match self.stage_registers.idex {
                IdEx::Flush | IdEx::Stall => {
                    self.stage_registers.exmem = ExMem::Flush;

                    return Ok(());
                }
                IdEx::Id {
                    instruction,
                    read_data_1,
                    read_data_2,
                    immediate,
                    pc,
                    control_signals,
                    ..
                } => (
                    instruction,
                    read_data_1,
                    read_data_2,
                    immediate,
                    pc,
                    control_signals,
                ),
            };

        // ALU control unit
        let alu_control = alu_control_unit(
            control_signals.alu_op,
            instruction.funct3(),
            instruction.funct7(),
        )?;

        // forwarding unit
        let (forward_a, forward_b) = forwarding_unit(
            self.stage_registers.exmem,
            self.stage_registers.wb_stage,
            self.stage_registers.idex,
        );

        // data forwarding
        let read_data_1 = match (
            forward_a,
            self.stage_registers.exmem,
            self.stage_registers.wb_stage,
        ) {
            (ForwardA::ExMem, ExMem::Ex { alu_result, .. }, _) => Some(alu_result),
            (ForwardA::MemWb, _, Wb::Mem { wb_data, .. }) => wb_data,
            _ => read_data_1,
        };
        let read_data_2 = match (
            forward_b,
            self.stage_registers.exmem,
            self.stage_registers.wb_stage,
        ) {
            (ForwardB::ExMem, ExMem::Ex { alu_result, .. }, _) => Some(alu_result),
            (ForwardB::MemWb, _, Wb::Mem { wb_data, .. }) => wb_data,
            _ => read_data_2,
        };

        // ALU operation
        let alu_operand_a: u32 = match control_signals.alu_src_a {
            ALUSrcA::Register => read_data_1.unwrap(),
            ALUSrcA::PC => pc,
            ALUSrcA::Constant0 => 0,
        };
        let alu_operand_b: u32 = match control_signals.alu_src_b {
            ALUSrcB::Register => read_data_2.unwrap(),
            ALUSrcB::Immediate => match immediate {
                #[allow(clippy::cast_sign_loss)]
                Immediate::SignedImmediate(imm) | Immediate::JumpOffset(imm) => imm as u32,
                Immediate::BranchOffset(_) => {
                    bail!("branch offset should not be used as ALU operand")
                }
                Immediate::UpperImmediate(imm) => imm,
                Immediate::None => bail!("no immediate value found"),
            },
            ALUSrcB::Constant4 => 4,
        };

        let (alu_zero, alu_result) = alu(alu_control, alu_operand_a, alu_operand_b);

        // signal used by the branch and jump unit to help it resolve the branch or jump instruction
        let operands_equal = alu_operand_a == alu_operand_b;

        // branch and jump address calculation
        let pc_src = branching_jump_unit(
            control_signals.branch_jump,
            alu_control,
            alu_result,
            alu_zero,
            operands_equal,
            instruction.funct3(),
            immediate,
        )?;

        // set the EX/MEM stage registers
        self.stage_registers.exmem = ExMem::Ex {
            instruction,
            alu_result,
            alu_zero,
            read_data_2,
            pc_src,
            pc,
            control_signals,
        };
        Ok(())
    }

    /// the Memory stage of the CPU.
    ///
    /// This function will read or write to the data memory based on the control signals.
    ///
    /// # Returns
    ///
    /// a report of what happened in the CPU during the memory stage
    fn mem(&mut self) -> String {
        // if the execute stage failed, flush
        let (instruction, alu_result, read_data_2, pc, control_signals) =
            match self.stage_registers.exmem {
                ExMem::Flush => {
                    self.stage_registers.memwb = MemWb::Flush;
                    return String::new();
                }
                ExMem::Ex {
                    instruction,
                    alu_result,
                    read_data_2,
                    pc_src,
                    pc,
                    control_signals,
                    ..
                } => {
                    // if the branch and jump unit told us to take a branch or jump, we need to flush the pipeline
                    match pc_src {
                        PCSrc::BranchTarget { .. } | PCSrc::JumpTarget { .. } => {
                            self.stage_registers.ifid = IfId::Flush;
                            self.stage_registers.idex = IdEx::Flush;
                            self.if_flush = true;
                        }
                        _ => (),
                    }
                    self.pc_src = pc_src;
                    (instruction, alu_result, read_data_2, pc, control_signals)
                }
            };

        let (memwb, report) = match (control_signals.mem_read, control_signals.mem_write) {
            (true, false) => {
                // load
                let mem_read_data = self.d_mem.read(alu_result);
                (
                    MemWb::Mem {
                        instruction,
                        alu_result,
                        mem_read_data: Some(mem_read_data),
                        pc,
                        control_signals,
                    },
                    String::new(),
                )
            }
            (false, true) => {
                // store
                self.d_mem
                    .write(alu_result, read_data_2.expect("no data to store"));
                (
                    MemWb::Mem {
                        instruction,
                        alu_result,
                        mem_read_data: None,
                        pc,
                        control_signals,
                    },
                    format!(
                        "memory 0x{:x} is modified to 0x{:x}\n",
                        alu_result,
                        read_data_2.expect("no data to store")
                    ),
                )
            }
            (false, false) => {
                // no memory operation
                (
                    MemWb::Mem {
                        instruction,
                        alu_result,
                        mem_read_data: None,
                        pc,
                        control_signals,
                    },
                    String::new(),
                )
            }
            (true, true) => panic!("invalid control signals for memory stage"),
        };

        self.stage_registers.memwb = memwb;

        report
    }

    /// the Write Back stage of the CPU.
    ///
    /// This function will write the result of the ALU operation or the memory read data to the register file.
    ///
    /// # Returns
    ///
    /// a report of what happened in the CPU during the write back stage
    fn write_back(&mut self) -> String {
        // if the memory stage failed, flush
        let (instruction, alu_result, mem_read_data, pc, control_signals) =
            match self.stage_registers.memwb {
                MemWb::Flush => {
                    self.stage_registers.wb_stage = Wb::Flush;
                    return String::new();
                }
                MemWb::Mem {
                    instruction,
                    alu_result,
                    mem_read_data,
                    pc,
                    control_signals,
                } => (instruction, alu_result, mem_read_data, pc, control_signals),
            };

        match (control_signals.reg_write, instruction.rd()) {
            (true, Some(rd)) => {
                // write to register file
                match control_signals.wb_src {
                    crate::signals::WriteBackSrc::NA => {
                        self.stage_registers.wb_stage = Wb::Mem {
                            instruction,
                            wb_data: None,
                            control_signals,
                        };
                        String::new()
                    }
                    crate::signals::WriteBackSrc::ALU => {
                        self.stage_registers.wb_stage = Wb::Mem {
                            instruction,
                            wb_data: Some(alu_result),
                            control_signals,
                        };
                        // write the ALU result to the register file
                        self.rf.write(rd, alu_result);
                        format!("{rd} is modified to 0x{alu_result:x}\n")
                    }
                    crate::signals::WriteBackSrc::Mem => {
                        self.stage_registers.wb_stage = Wb::Mem {
                            instruction,
                            wb_data: mem_read_data,
                            control_signals,
                        };
                        // write the memory read data to the register file
                        self.rf.write(rd, mem_read_data.expect("no data to write"));
                        format!(
                            "{rd} is modified to 0x{:x}\n",
                            mem_read_data.expect("no data to write")
                        )
                    }
                    crate::signals::WriteBackSrc::PC => {
                        self.stage_registers.wb_stage = Wb::Mem {
                            instruction,
                            wb_data: Some(pc + 4),
                            control_signals,
                        };
                        self.rf.write(rd, pc + 4);
                        format!("{rd} is modified to 0x{:x}\n", pc + 4)
                    }
                }
            }
            (true, None) | (false, _) => {
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
    alu_control: ALUControl,
    alu_result: u32,
    alu_zero: bool,
    operands_equal: bool,
    funct3: Option<u3>,
    immediate: Immediate,
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
                ) => Ok(
                    match immediate {
                        Immediate::BranchOffset(offset) => PCSrc::BranchTarget{offset},
                        _ => return Err(anyhow::anyhow!("invalid immediate value\n")),
                    }
                ),

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
        BranchJump::Jal => Ok(PCSrc::JumpTarget { target: alu_result }),
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

        assert_eq!(cpu.stage_registers, StageRegisters::default());
        assert_eq!(cpu.pc_src, PCSrc::Init);
        assert_eq!(cpu.total_clock_cycles, 0);
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

        let _ = cpu.fetch();

        match cpu.stage_registers.ifid {
            IfId::If {
                instruction_code,
                pc,
            } => {
                assert_eq!(pc, 0);
                assert_eq!(instruction_code, 0x00000013);
            }
            _ => panic!("expected IFID::If"),
        }

        let _ = cpu.fetch();

        match cpu.stage_registers.ifid {
            IfId::If {
                instruction_code,
                pc,
            } => {
                assert_eq!(instruction_code, 0x00000093);
                assert_eq!(pc, 4);
            }
            _ => panic!("expected IFID::If"),
        }

        let _ = cpu.fetch();

        match cpu.stage_registers.ifid {
            IfId::If {
                instruction_code,
                pc,
            } => {
                assert_eq!(instruction_code, 0x00000073);
                assert_eq!(pc, 8);
            }
            _ => panic!("expected IFID::If"),
        }

        let _ = cpu.fetch();

        match cpu.stage_registers.ifid {
            IfId::If {
                instruction_code,
                pc,
            } => {
                assert_eq!(instruction_code, 0x00000033);
                assert_eq!(pc, 12);
            }
            _ => panic!("expected IFID::If"),
        }
    }

    #[test]
    fn test_cpu_decode() {
        let rom = vec![0x00000013];
        let mut cpu = CPU::new(rom);

        let _ = cpu.fetch();
        cpu.decode().unwrap();

        match cpu.stage_registers.idex {
            IdEx::Id {
                instruction,
                read_data_1,
                read_data_2,
                immediate,
                ..
            } => {
                assert_eq!(
                    instruction,
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
                assert_eq!(read_data_1, Some(0));
                assert_eq!(read_data_2, None);
                assert_eq!(immediate, Immediate::SignedImmediate(0));
            }
            _ => panic!("expected IDEX::Id"),
        }
    }

    #[test]
    fn test_cpu_execute() {
        let rom = vec![0x00000013];
        let mut cpu = CPU::new(rom);

        let _ = cpu.fetch();
        cpu.decode().unwrap();
        cpu.execute().unwrap();

        match cpu.stage_registers.exmem {
            ExMem::Ex {
                instruction,
                alu_result,
                alu_zero,
                read_data_2,
                ..
            } => {
                assert_eq!(
                    instruction,
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
                assert_eq!(alu_result, 0);
                assert_eq!(alu_zero, true);
                assert_eq!(read_data_2, None);
                assert_eq!(cpu.pc_src, PCSrc::Next);
            }
            _ => panic!("expected EXMEM::Ex"),
        }
    }

    #[test]
    fn test_cpu_mem() {
        // this instruction will load the value at offset 4 from the address in register T2 (0) into register T0
        let rom = vec![0x0043_A283];
        let mut cpu = CPU::new(rom);

        // put some data in the data memory
        cpu.d_mem.write(0, 5);
        cpu.d_mem.write(4, 10);
        cpu.d_mem.write(8, 15);

        let _ = cpu.fetch();
        cpu.decode().unwrap();
        cpu.execute().unwrap();
        let _ = cpu.mem();

        match cpu.stage_registers.memwb {
            MemWb::Mem {
                instruction,
                alu_result,
                mem_read_data,
                pc: _,
                control_signals: _,
            } => {
                assert_eq!(
                    instruction,
                    Instruction::IType {
                        funct7: None,
                        shamt: None,
                        opcode: u7::new(0b0000011),
                        rd: RegisterMapping::T0,
                        funct3: u3::new(2),
                        rs1: RegisterMapping::T2,
                        imm: i12::new(4),
                    }
                );
                assert_eq!(alu_result, 4);
                assert_eq!(mem_read_data, Some(10));
                assert_eq!(cpu.pc_src, PCSrc::Next);
            }
            _ => panic!("expected MEMWB::Mem"),
        }
    }

    #[test]
    fn test_cpu_write_back() {
        // this instruction will load the value at offset 4 from the address in register T2 into register T0
        let rom = vec![0x0043_A283];
        let mut cpu = CPU::new(rom);

        // put some data in the data memory
        cpu.d_mem.write(4, 10);

        let _ = cpu.fetch();
        cpu.decode().unwrap();
        cpu.execute().unwrap();
        let _ = cpu.mem();
        cpu.write_back();

        assert_eq!(cpu.pc_src, PCSrc::Next);

        assert_eq!(cpu.rf.read(RegisterMapping::T0), 10);
    }

    #[test]
    fn test_data_load_hazard() {
        let rom = vec![
            0x007302b3, // add t0, t1, t2 // t0 = 3 + 7 = 10
            0x41c28e33, // sub t3, t0, t3 // t3 = 10 - 11 = -1
            0x01f2feb3, // and t4, t0, t6 // t4 = 10 & 19 = 2
            0x01d2ef33, // or t5, t0, t4  // t5 = 10 | 2 = 10
            0x01eecfb3, // xor t6, t4, t5 // t6 = 10 ^ 2 = 8
        ];
        // (expected) pipeline table
        // | cycle | IF | ID | EX | MEM | WB |
        // |-------|----|----|----|-----|----|
        // | 1     | I1 |    |    |     |    |
        // | 2     | I2 | I1 |    |     |    |
        // | 3     | I3 | I2 | I1 |     |    |
        // | 4     | I4 | I3 | I2 | I1  |    |
        // | 5     | I5 | I4 | I3 | I2  | I1 |
        // | 6     |    | I5 | I4 | I3  | I2 |
        // | 7     |    |    | I5 | I4  | I3 |
        // | 8     |    |    |    | I5  | I4 |
        // | 9     |    |    |    |     | I5 |

        let mut cpu = CPU::new(rom);
        // set up initial register values
        cpu.initialize_rf(&[
            (RegisterMapping::T0, 1),
            (RegisterMapping::T1, 3),
            (RegisterMapping::T2, 7),
            (RegisterMapping::T3, 11),
            (RegisterMapping::T4, 13),
            (RegisterMapping::T5, 17),
            (RegisterMapping::T6, 19),
        ]);

        let _ = cpu.run_step().expect("error in first cycle");
        let _ = cpu.run_step().expect("error in second cycle");
        let _ = cpu.run_step().expect("error in third cycle");
        let _ = cpu.run_step().expect("error in fourth cycle");
        let _ = cpu.run_step().expect("error in fifth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T0), 10);
        let _ = cpu.run_step().expect("error in sixth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T3), -1i32 as u32);
        let _ = cpu.run_step().expect("error in seventh cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T4), 2);
        let _ = cpu.run_step().expect("error in eighth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T5), 10);
        let _ = cpu.run_step().expect("error in ninth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T6), 8);
    }

    #[test]
    fn test_data_rtype_hazard() {
        let rom = vec![
            0x0002a303, // lw t1, 0(t0)   // t1 = 3
            0x007302b3, // add t0, t1, t2 // t0 = 3 + 7 = 10
            0x41c28e33, // sub t3, t0, t2 // t3 = 10 - 11 = -1
            0x01f2feb3, // and t4, t0, t6 // t4 = 10 & 19 = 2
            0x01d2ef33, // or t5, t0, t4  // t5 = 10 | 2 = 10
            0x01eecfb3, // xor t6, t4, t5 // t6 = 10 ^ 2 = 8
        ];
        // (expected) pipeline table
        // | cycle | IF | ID | EX | MEM | WB |
        // |-------|----|----|----|-----|----|
        // | 1     | I1 |    |    |     |    |
        // | 2     | I2 | I1 |    |     |    |
        // | 3     | I3 | I2 | I1 |     |    |
        // | 4     | I4 | I3 | I2 | I1  |    |
        // | 5     | I5 | I4 | I3 | I2  | I1 |
        // | 6     | I6 | I5 | I4 | I3  | I2 |
        // | 7     |    | I6 | I5 | I4  | I3 |
        // | 8     |    |    | I6 | I5  | I4 |
        // | 9     |    |    |    | I6  | I5 |
        // | 10    |    |    |    |     | I6 |

        let mut cpu = CPU::new(rom);
        // set up initial register values
        cpu.initialize_rf(&[
            (RegisterMapping::T0, 0),
            (RegisterMapping::T1, 0),
            (RegisterMapping::T2, 7),
            (RegisterMapping::T3, 11),
            (RegisterMapping::T4, 13),
            (RegisterMapping::T5, 17),
            (RegisterMapping::T6, 19),
        ]);
        // put some data in the data memory
        cpu.d_mem.write(0, 3);

        let _ = cpu.run_step().expect("error in first cycle");
        let _ = cpu.run_step().expect("error in second cycle");
        let stall_cycle = cpu.run_step().expect("error in third cycle");
        assert!(stall_cycle.contains("pipeline stalled in the decode stage"));
        let _ = cpu.run_step().expect("error in fourth cycle"); // stall
        let _ = cpu.run_step().expect("error in fifth cycle");
        let _ = cpu.run_step().expect("error in sixth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T1), 3);
        let _ = cpu.run_step().expect("error in seventh cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T0), 10);
        let _ = cpu.run_step().expect("error in eighth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T3), -1i32 as u32);
        let _ = cpu.run_step().expect("error in ninth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T4), 2);
        let _ = cpu.run_step().expect("error in tenth cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T5), 10);
        let _ = cpu.run_step().expect("error in eleventh cycle");
        assert_eq!(cpu.rf.read(RegisterMapping::T6), 8);
    }
}
