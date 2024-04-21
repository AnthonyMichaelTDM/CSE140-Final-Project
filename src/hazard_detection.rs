use crate::{
    instruction::Instruction,
    registers::RegisterMapping,
    stages::{EXMEM, IDEX, WB},
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a 2 bit signal that tells the forwarding unit what to forward to the ID/EX stage.
pub enum ForwardA {
    #[default]
    None = 0b00,
    EXMEM = 0b10,
    MEMWB = 0b01,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
/// a 2 bit signal that tells the forwarding unit what to forward to the ID/EX stage.
pub enum ForwardB {
    #[default]
    None = 0b00,
    EXMEM = 0b10,
    MEMWB = 0b01,
}

/// the forwarding unit determines whether to forward data from the EX/MEM and/or MEM/WB stages to the ID/EX stage.
pub fn forwarding_unit(exmem: EXMEM, wb: WB, idex: IDEX) -> (ForwardA, ForwardB) {
    // Initialize forwarding variables
    let mut forward_a = ForwardA::None;
    let mut forward_b = ForwardB::None;

    // Extract source registers from IDEX stage
    let (idex_source_reg1, idex_source_reg2) = match idex {
        IDEX::Id { rs1, rs2, .. } => (rs1, rs2),
        _ => (None, None),
    };

    // Extract register write and destination register from EXMEM stage
    let (exmem_regwrite, exmem_dest_reg) = match exmem {
        EXMEM::Ex {
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
        WB::Mem {
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
        Some(rs1) if exmem_regwrite && exmem_dest_reg == rs1 => forward_a = ForwardA::EXMEM,
        Some(rs1) if memwb_regwrite && memwb_dest_reg == rs1 => forward_a = ForwardA::MEMWB,
        _ => (),
    }

    // Determine forwarding for source register 2
    match idex_source_reg2 {
        None | Some(RegisterMapping::Zero) => (),
        Some(rs2) if exmem_regwrite && exmem_dest_reg == rs2 => forward_b = ForwardB::EXMEM,
        Some(rs2) if memwb_regwrite && memwb_dest_reg == rs2 => forward_b = ForwardB::MEMWB,
        _ => (),
    }

    // Return forwarding decisions
    (forward_a, forward_b)
}

/// The hazard detection unit determines whether there is a data hazard between the ID and EX stages that requires stalling (e.g. load data hazards)
/// (the forwarding unit handles rtype data hazards, and can handle load hazards if a stall was performed)
///
/// # Fields
///
/// * `ifid_rs1` - the source register 1 from the IF/ID stage
/// * `ifid_rs2` - the source register 2 from the IF/ID stage
/// * `idex_rd` - the destination register from the ID/EX stage
/// * `idex_memread` - a boolean indicating whether the instruction in the ID/EX stage writes to memory
pub struct HazardDetectionUnit {
    ifid_rs1: Option<RegisterMapping>,
    ifid_rs2: Option<RegisterMapping>,
    idex_rd: Option<RegisterMapping>,
    idex_memread: bool,
}

impl HazardDetectionUnit {
    /// prime the hazard detection unit with the relevant current pipeline state
    pub fn prime(decoded_instruction: Instruction, idex_reg: IDEX) -> Self {
        let ifid_rs1 = decoded_instruction.rs1();
        let ifid_rs2 = decoded_instruction.rs2();

        let idex_rd = match idex_reg {
            IDEX::Id { instruction, .. } => instruction.rd(),
            _ => None,
        };

        let idex_memread = match idex_reg {
            IDEX::Id {
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
