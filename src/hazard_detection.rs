use crate::{
    instruction::Instruction,
    registers::RegisterMapping,
    stages::{ExMem, IdEx, Wb},
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a 2 bit signal that tells the forwarding unit what to forward to the ID/EX stage.
pub enum ForwardA {
    #[default]
    None = 0b00,
    ExMem = 0b10,
    MemWb = 0b01,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a 2 bit signal that tells the forwarding unit what to forward to the ID/EX stage.
pub enum ForwardB {
    #[default]
    None = 0b00,
    ExMem = 0b10,
    MemWb = 0b01,
}

/// The forwarding unit determines whether to forward data from the EX/MEM and/or MEM/WB stages to the ID/EX stage.
///
/// # Arguments
///
/// * `exmem` - the values in the EX/MEM pipeline stage register.
/// * `wb` - the values in the MEM/WB pipeline stage register.
/// * `idex` - the values in the ID/EX pipeline stage register.
///
/// # Returns
///
/// * `ForwardA` - the forwarding decision for source register 1.
/// * `ForwardB` - the forwarding decision for source register 2.
pub fn forwarding_unit(exmem: ExMem, wb: Wb, idex: IdEx) -> (ForwardA, ForwardB) {
    // Initialize forwarding variables
    let mut forward_a = ForwardA::None;
    let mut forward_b = ForwardB::None;

    // Extract source registers from IDEX stage
    let (idex_source_reg1, idex_source_reg2) = match idex {
        IdEx::Id { rs1, rs2, .. } => (rs1, rs2),
        _ => (None, None),
    };

    // Extract register write and destination register from EXMEM stage
    let (exmem_regwrite, exmem_dest_reg) = match exmem {
        ExMem::Ex {
            control_signals,
            instruction,
            ..
        } if instruction.rd().is_some() && instruction.rd().unwrap() != RegisterMapping::Zero => {
            (control_signals.reg_write, instruction.rd().unwrap())
        }
        _ => (false, RegisterMapping::Zero),
    };

    // Extract register write and destination register from MEMWB stage
    let (memwb_regwrite, memwb_dest_reg) = match wb {
        Wb::Mem {
            control_signals,
            instruction,
            ..
        } if instruction.rd().is_some() && instruction.rd().unwrap() != RegisterMapping::Zero => {
            (control_signals.reg_write, instruction.rd().unwrap())
        }
        _ => (false, RegisterMapping::Zero),
    };

    // Determine forwarding for source register 1
    match idex_source_reg1 {
        None | Some(RegisterMapping::Zero) => (),
        Some(rs1) if exmem_regwrite && exmem_dest_reg == rs1 => forward_a = ForwardA::ExMem,
        Some(rs1) if memwb_regwrite && memwb_dest_reg == rs1 => forward_a = ForwardA::MemWb,
        _ => (),
    }

    // Determine forwarding for source register 2
    match idex_source_reg2 {
        None | Some(RegisterMapping::Zero) => (),
        Some(rs2) if exmem_regwrite && exmem_dest_reg == rs2 => forward_b = ForwardB::ExMem,
        Some(rs2) if memwb_regwrite && memwb_dest_reg == rs2 => forward_b = ForwardB::MemWb,
        _ => (),
    }

    // Return forwarding decisions
    (forward_a, forward_b)
}

/// The hazard detection unit determines whether there is a data hazard between the ID and EX stages that requires stalling (e.g. load-use hazards)
/// (the forwarding unit handles rtype data hazards, and can handle load hazards if a stall was performed)
#[allow(clippy::module_name_repetitions)]
pub struct HazardDetectionUnit {
    /// the source register 1 from the IF/ID stage
    ifid_rs1: Option<RegisterMapping>,
    /// the source register 2 from the IF/ID stage
    ifid_rs2: Option<RegisterMapping>,
    /// the destination register from the ID/EX stage
    idex_rd: Option<RegisterMapping>,
    /// a boolean indicating whether the instruction in the ID/EX stage writes to memory
    idex_memread: bool,
}

impl HazardDetectionUnit {
    /// prime the hazard detection unit with the relevant current pipeline state
    pub const fn prime(decoded_instruction: Instruction, idex_reg: IdEx) -> Self {
        let ifid_rs1 = decoded_instruction.rs1();
        let ifid_rs2 = decoded_instruction.rs2();

        let idex_rd = match idex_reg {
            IdEx::Id { instruction, .. } => instruction.rd(),
            _ => None,
        };

        let idex_memread = match idex_reg {
            IdEx::Id {
                control_signals, ..
            } => control_signals.mem_read,
            _ => false,
        };

        Self {
            ifid_rs1,
            ifid_rs2,
            idex_rd,
            idex_memread,
        }
    }

    /// Detect whether a stall is required to resolve a data hazard
    pub fn detect_stall_conditions(self) -> bool {
        // check for a hazard with rs1
        let rs1_hazard = match (self.ifid_rs1, self.idex_rd, self.idex_memread) {
            // hazard in the ID/EX stage
            (Some(rs1), Some(rd), true) if rs1 == rd => true,
            _ => false,
        };

        // check for a hazard with rs2
        let rs2_hazard = match (self.ifid_rs2, self.idex_rd, self.idex_memread) {
            // hazard in the ID/EX stage
            (Some(rs2), Some(rd), true) if rs2 == rd => true,
            _ => false,
        };

        // return whether a stall is required
        rs1_hazard || rs2_hazard
    }
}
