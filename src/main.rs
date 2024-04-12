use anyhow::{anyhow, Result};
use cse140_final_project_riscv::{
    cpu::CPU,
    registers::RegisterMapping,
    utils::{bit_vec_from_string, bit_vec_to_int},
};

fn main() -> Result<()> {
    // first, ask the user what file they want to run
    println!("Enter the name of the file name to run:\n");
    let mut file_name = String::new();
    std::io::stdin().read_line(&mut file_name).unwrap();
    let file_name = file_name.trim();

    // we only have 2 valid files, and each has a separate initial state for the registers.
    // ideally, we'd let the users choose which of the two files to run, but that might not align with the project requirements
    // so we'll just hardcode the initial state for each file, and throw an error if the user tries to run a different file
    let register_mappings = match file_name {
        "sample_part1.txt" => vec![
            (RegisterMapping::Ra, 0x20u32),
            (RegisterMapping::Sp, 0x5),
            (RegisterMapping::A0, 0x70),
            (RegisterMapping::A1, 0x4),
        ],
        "sample_part2.txt" => vec![
            (RegisterMapping::S0, 0x20),
            (RegisterMapping::A0, 0x5),
            (RegisterMapping::A1, 0x2),
            (RegisterMapping::A2, 0xa),
            (RegisterMapping::A3, 0xf),
        ],
        _ => return Err(anyhow!("Invalid file name")),
    };

    if file_name != "sample_part1.txt" && file_name != "sample_part2.txt" {
        return Err(anyhow!("Invalid file name"));
    }

    // read the file
    let file = std::fs::read_to_string(file_name)?;

    // parse the file
    let i_mem = file
        .split("\n")
        .map(|line| bit_vec_from_string(line).map(|bits| bit_vec_to_int(&bits)))
        .collect::<Result<Vec<u32>>>()?;

    // Initialize the CPU state
    let mut cpu = CPU::new(i_mem);
    cpu.initialize_rf(&register_mappings);

    // Run the CPU
    cpu.run();

    Ok(())
}
