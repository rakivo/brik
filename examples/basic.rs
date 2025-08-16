use brik::rv32::Reg::*;
use brik::asm::Assembler;
use brik::asm::arch::Arch;
use brik::object::{
    Endianness,
    SymbolKind,
    SymbolFlags,
    SymbolScope,
    BinaryFormat,
};
use brik::object::write::{
    Object,
    FileFlags
};

use std::{fs, env, error};

fn produce_add_34_35_obj<'a>() -> Object<'a> {
    let mut asm = Assembler::new(
        BinaryFormat::Elf,
        Arch::Riscv64,
        Endianness::Little,
        "rv64gc"
    );

    asm.set_object_flags(FileFlags::Elf {
        os_abi: 0,
        abi_version: 0,
        e_flags: 0x4,
    });

    // .rodata section for format string
    let _rodata = asm.add_rodata_section_at_end();

    let fmt_sym = asm.define_data("fmt", b"34 + 35 = %d\n\0");

    let printf_sym = asm.add_symbol_extern(
        b"printf",
        SymbolKind::Text,
        SymbolScope::Dynamic
    );

    let text_section = asm.add_text_section_at_end();

    asm.emit_function_prologue();

    // a0 = fmt
    asm.emit_pcrel_load_addr(A0, fmt_sym);

    // a1 = 34
    asm.emit_li(A1, 34);

    // a1 += 35
    asm.emit_addi(A1, A1, 35);

    asm.emit_call_plt(printf_sym);

    asm.emit_function_epilogue();
    asm.emit_return_imm(0);

    asm.add_symbol(
        b"main",
        0,
        asm.section_size(text_section) as _,
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

    let obj = produce_add_34_35_obj();

    let file = fs::File::create(output_path)?;
    obj.write_stream(&file)?;

    println!("[wrote object file to {output_path}]");

    Ok(())
}

