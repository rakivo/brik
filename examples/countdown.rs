use brik::rv64;
use brik::asm::Assembler;
use brik::rv32::{I, Reg};
use brik::object::{
    Endianness,
    SymbolKind,
    SymbolScope,
    SectionKind,
    Architecture,
    BinaryFormat,
};
use brik::object::write::{
    Object,
    FileFlags,
    StandardSegment,
};

use std::{fs, env, mem, error};

fn produce_countdown_obj<'a>() -> Object<'a> {
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

    let _rodata = asm.add_section_at_end(
        StandardSegment::Data,
        b".rodata",
        SectionKind::ReadOnlyData,
    );

    let msg_bytes = b"Hello from RISC-V\n\0";
    let msg_offset = asm.emit_bytes(msg_bytes);
    let msg_sym = asm.add_symbol(
        b"msg",
        msg_offset,
        msg_bytes.len() as u64,
        SymbolKind::Data,
        SymbolScope::Compilation,
    );

    let countdown_constant = 10u64;
    let countdown_offset = asm.emit_bytes(countdown_constant);
    let countdown_sym = asm.add_symbol(
        b"countdown",
        countdown_offset,
        mem::size_of_val(&countdown_constant) as _,
        SymbolKind::Data,
        SymbolScope::Compilation,
    );

    let printf_sym = asm.add_symbol_extern(
        b"printf",
        SymbolKind::Text,
        SymbolScope::Dynamic
    );

    let text_section = asm.add_section_at_end(
        StandardSegment::Text,
        b".text",
        SectionKind::Text,
    );

    asm.emit_function_prologue();

    // s1 = count
    asm.emit_pcrel_load_addr(Reg::S1, countdown_sym);
    asm.emit_bytes(rv64::encode_ld(Reg::S1, Reg::S1, 0));

    let loop_lbl = asm.add_label_here(b".loop");

    // a0 = msg
    asm.emit_pcrel_load_addr(Reg::A0, msg_sym);

    asm.emit_call_plt(printf_sym);

    // s1 -= 1
    asm.emit_bytes(
        I::ADDI {
            d: Reg::S1,
            s: Reg::S1,
            im: -1
        }
    );

    // blt 0, s1
    asm.emit_branch_to(
        loop_lbl,
        I::BLT {
            s1: Reg::ZERO,
            s2: Reg::S1,
            im: 0
        }
    );

    asm.emit_function_epilogue();
    asm.emit_return_imm(0);

    asm.add_symbol(
        b"main",
        0,
        asm.section_size(text_section) as _,
        SymbolKind::Text,
        SymbolScope::Dynamic,
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
