use brik::rv32::I32::*;
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

fn produce_countdown_obj<'a>() -> Object<'a> {
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

    // .rodata section strings
    let _rodata = asm.add_rodata_section_at_end();

    let msg_sym = asm.define_data("msg", b"Hello from RISC-V\n\0");
    let countdown_sym = asm.define_data("countdown", 10u64);

    let printf_sym = asm.add_symbol_extern(
        b"printf",
        SymbolKind::Text,
        SymbolScope::Dynamic
    );

    let text_section = asm.add_text_section_at_end();

    asm.emit_function_prologue();

    // s1 = count
    asm.emit_pcrel_load_addr(S1, countdown_sym, 0);
    asm.emit_ld(S1, S1, 0);

    let loop_lbl = asm.add_label_here(
        b".loop",
        SymbolKind::Text,
        SymbolScope::Compilation
    );

    // a0 = msg
    asm.emit_pcrel_load_addr(A0, msg_sym, 0);

    asm.emit_call_plt(printf_sym);

    // s1 -= 1
    asm.emit_addi(S1, S1, -1);

    // blt 0, s1
    asm.emit_branch_to(
        loop_lbl,
        BLT {
            s1: ZERO,
            s2: S1,
            im: 0
        }
    );

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

    let obj = produce_countdown_obj();

    let file = fs::File::create(output_path)?;
    obj.write_stream(&file)?;

    println!("[wrote object file to {output_path}]");

    Ok(())
}
