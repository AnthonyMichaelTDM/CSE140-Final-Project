pub mod alu;
pub mod cpu;
pub mod instruction;
pub mod registers;
pub mod signals;
pub mod stages;
pub mod utils;

#[cfg(test)]
mod tests {
    use super::*;

    use anyhow::Result;
    use pretty_assertions::assert_eq;

    fn sample1_rom() -> Vec<u32> {
        let mut rom = include_str!("../sample_part1.txt")
            .split("\n")
            .map(|line| utils::bit_vec_from_string(line).map(|bits| utils::bit_vec_to_int(&bits)))
            .collect::<Result<Vec<u32>>>()
            .unwrap();
        // handle the case where the last line is empty
        if rom.last() == Some(&0) {
            rom.pop();
        }
        rom
    }

    fn sample2_rom() -> Vec<u32> {
        let mut rom = include_str!("../sample_part2.txt")
            .split("\n")
            .map(|line| utils::bit_vec_from_string(line).map(|bits| utils::bit_vec_to_int(&bits)))
            .collect::<Result<Vec<u32>>>()
            .unwrap();
        // handle the case where the last line is empty
        if rom.last() == Some(&0) {
            rom.pop();
        }
        rom
    }

    fn sample1_rf() -> Vec<(registers::RegisterMapping, u32)> {
        vec![
            (registers::RegisterMapping::Ra, 0x20u32),
            (registers::RegisterMapping::Sp, 0x5),
            (registers::RegisterMapping::A0, 0x70),
            (registers::RegisterMapping::A1, 0x4),
        ]
    }

    fn sample2_rf() -> Vec<(registers::RegisterMapping, u32)> {
        vec![
            (registers::RegisterMapping::S0, 0x20),
            (registers::RegisterMapping::A0, 0x5),
            (registers::RegisterMapping::A1, 0x2),
            (registers::RegisterMapping::A2, 0xa),
            (registers::RegisterMapping::A3, 0xf),
        ]
    }

    fn sample1_dmem() -> Vec<(u32, u32)> {
        vec![(0x70, 0x5), (0x74, 0x10)]
    }

    #[test]
    fn test_sample_1() -> Result<()> {
        let mut cpu = cpu::CPU::new(sample1_rom());
        cpu.initialize_rf(&sample1_rf());
        cpu.initialize_dmem(&sample1_dmem());

        assert_eq!(
            "total_clock_cycles 1 :\nx3 is modified to 0x10\npc is modified to 0x4\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 2 :\nx5 is modified to 0x1b\npc is modified to 0x8\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 3 :\npc is modified to 0xc\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 4 :\nx5 is modified to 0x2b\npc is modified to 0x10\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 5 :\nx5 is modified to 0x2f\npc is modified to 0x14\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 6 :\nmemory 0x70 is modified to 0x2f\npc is modified to 0x18\n",
            cpu.run_step()?
        );

        Ok(())
    }

    #[test]
    fn test_sample_2() -> Result<()> {
        let mut cpu = cpu::CPU::new(sample2_rom());
        cpu.initialize_rf(&sample2_rf());

        assert_eq!(
            "total_clock_cycles 1 :\nx1 is modified to 0x4\npc is modified to 0x8\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 2 :\nx10 is modified to 0xc\npc is modified to 0xc\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 3 :\nx30 is modified to 0x3\npc is modified to 0x10\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 4 :\nx1 is modified to 0x14\npc is modified to 0x4\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 5 :\nx1 is modified to 0x8\npc is modified to 0x14\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 6 :\nmemory 0x20 is modified to 0x3\npc is modified to 0x18\n",
            cpu.run_step()?
        );

        Ok(())
    }
}
