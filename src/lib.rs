pub mod alu;
pub mod cpu;
mod hazard_detection;
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
        // just in case the last line is empty
        if rom.last() == Some(&0) {
            rom.pop();
        }

        rom

        // sample 1 is the following:
        // 00000000010001010010000110000011 // lw x3, 4(x10) // x3 = 0x10
        // 01000000001000001000001010110011 // sub x5, x1, x2 // x5 = x1 - x2 = 0x20 - 0x5 = 0x1b
        // 00000000001100101000011001100011 // beq x5, x3, 12 // not taken
        // 00000000001100101000001010110011 // add x5, x5, x3 // x5 = 0x1b + 0x10 = 0x2b
        // 00000000010101011110001010110011 // or x5, x5, x11 // x5 = 0x2b | 0x4 = 0x2f
        // 00000000010101010010000000100011 // sw x5, 0(x10) // memory[0x70] = 0x2f

        // pipeline table (expected):
        // | cycle | IF | ID | EX | MEM | WB |   | PC |
        // |-------|----|----|----|-----|----|--|----|
        // | 1     | I1 |    |    |     |    |  | 0  |
        // | 2     | I2 | I1 |    |     |    |  | 4  |
        // | 3     | I3 | I2 | I1 |     |    |  | 8  |
        // | 4     | I4 | I3 | I2 | I1  |    |  | 12 |
        // | 5     | I5 | I4 | I3 | I2  | I1 |  | 16 |
        // | 6     | I6 | I5 | I4 | I3  | I2 |  | 20 |
        // | 7     |    | I6 | I5 | I4  | I3 |
        // | 8     |    |    | I6 | I5  | I4 |
        // | 9     |    |    |    | I6  | I5 |
        // | 10    |    |    |    |     | I6 |
    }

    #[test]
    fn test_sample_1_rom() {
        assert_eq!(
            sample1_rom(),
            vec![
                0b00000000010001010010000110000011,
                0b01000000001000001000001010110011,
                0b00000000001100101000011001100011,
                0b00000000001100101000001010110011,
                0b00000000010101011110001010110011,
                0b00000000010101010010000000100011,
            ]
        )
    }

    fn sample2_rom() -> Vec<u32> {
        let mut rom = include_str!("../sample_part2.txt")
            .split("\n")
            .map(|line| utils::bit_vec_from_string(line).map(|bits| utils::bit_vec_to_int(&bits)))
            .collect::<Result<Vec<u32>>>()
            .unwrap();

        // just in case the last line is empty
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

        assert_eq!("total_clock_cycles 1 :\n", cpu.run_step()?);
        assert_eq!(
            "total_clock_cycles 2 :\npc is modified to 0x4\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 3 :\npc is modified to 0x8\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 4 :\npc is modified to 0xc\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 5 :\nx3 is modified to 0x10\npc is modified to 0x10\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 6 :\nx5 is modified to 0x1b\npc is modified to 0x14\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 7 :\npc is modified to 0x18\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 8 :\nx5 is modified to 0x2b\npc is modified to 0x1c\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 9 :\nmemory 0x70 is modified to 0x2f\nx5 is modified to 0x2f\npc is modified to 0x20\n",
            cpu.run_step()?
        );
        assert_eq!(
            "total_clock_cycles 10 :\npc is modified to 0x24\n",
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
