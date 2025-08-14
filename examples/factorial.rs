use brik::rv64;
use brik::rv32::{I, Reg};
use brik::asm::Assembler;
use brik::object::{
    Endianness,
    SymbolKind,
    SymbolScope,
    SymbolFlags,
    Architecture,
    BinaryFormat,
};
use brik::object::write::{
    Object,
    FileFlags,
};

use std::{fs, env, error};

fn produce_factorial_obj<'a>() -> Object<'a> {
    let mut asm = Assembler::new(
        BinaryFormat::Elf,
        Architecture::Riscv64,
        Endianness::Little,
        "rv64gc"
    );

    asm.set_object_flags(FileFlags::Elf {
        os_abi: 0,
        abi_version: 0,
        e_flags: 0x4,
    });

    // .rodata section for format strings
    let _rodata = asm.add_rodata_section_at_end();

    let input_fmt_sym = asm.define_data(b"input_fmt", b"enter a number: \0");

    let scanf_fmt_sym = asm.define_data(b"scanf_fmt", b"%ld\0");

    let result_fmt_sym = asm.define_data(b"result_fmt", b"factorial: %ld\n\0");

    // external symbols

    let printf_sym = asm.add_symbol_extern(
        b"printf",
        SymbolKind::Text,
        SymbolScope::Dynamic
    );

    let scanf_sym = asm.add_symbol_extern(
        b"scanf",
        SymbolKind::Text,
        SymbolScope::Dynamic
    );

    let text_section = asm.add_text_section_at_end();

    asm.emit_function_prologue();

    // allocate space on stack for input number (8 bytes)
    asm.emit_addi(Reg::SP, Reg::SP, -8);

    // print input prompt
    asm.emit_pcrel_load_addr(Reg::A0, input_fmt_sym);
    asm.emit_call_plt(printf_sym);

    // read input number
    asm.emit_pcrel_load_addr(Reg::A0, scanf_fmt_sym);
    asm.emit_addi(Reg::A1, Reg::SP, 0);
    asm.emit_call_plt(scanf_sym);

    // load input number into s1
    asm.emit_ld(Reg::S1, Reg::SP, 0);

    // init factorial result in s2 (result = 1)
    asm.emit_addi(Reg::S2, Reg::ZERO, 1);

    // init counter in s3 (i = 1)
    asm.emit_addi(Reg::S3, Reg::ZERO, 1);

    let loop_lbl = asm.add_label_here(b".fact_loop");
    let done_lbl = asm.declare_label(b".fact_done");

    // loop condition: if i > n, exit
    asm.emit_branch_to(
        done_lbl,
        // if s1 < s3 (n < i)
        I::BLT { s1: Reg::S1, s2: Reg::S3, im: 0 },
    );

    // result *= i
    asm.emit_bytes(rv64::encode_mul(Reg::S2, Reg::S2, Reg::S3));

    // i++
    asm.emit_addi(Reg::S3, Reg::S3, 1);

    // jump back to loop
    asm.emit_branch_to(
        loop_lbl,
        I::JAL { d: Reg::ZERO, im: 0 },
    );

    asm.place_label_here(done_lbl);

    // print result
    asm.emit_pcrel_load_addr(Reg::A0, result_fmt_sym);
    asm.emit_mv(Reg::A1, Reg::S2); // move result to a1
    asm.emit_addi(Reg::A1, Reg::S2, 0);
    asm.emit_call_plt(printf_sym);

    // restore stack and return
    asm.emit_addi(Reg::SP, Reg::SP, 8);
    asm.emit_function_epilogue();
    asm.emit_return_imm(0);

    asm.add_symbol(
        b"main",
        0,
        asm.section_size(text_section),
        SymbolKind::Text,
        SymbolScope::Dynamic,
        false,
        SymbolFlags::None
    );

    asm.finish().unwrap()
}

fn main() -> Result<(), Box<dyn error::Error>> {
    let args = env::args().collect::<Vec<_>>();

    let Some(output_path) = args.get(1) else {
        println!{
            "usage: {prog} <output.o>",
            prog = args[0]
        };
        return Ok(())
    };

    let obj = produce_factorial_obj();

    let file = fs::File::create(output_path)?;
    obj.write_stream(&file)?;

    println!("[wrote object file to {output_path}]");

    Ok(())
}
