use brik::util::rv64;
use brik::asm::Assembler;
use brik::asm_riscv::{I, Reg};
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

    let _rodata = asm.add_section_at_end(
        StandardSegment::Data,
        b".rodata",
        SectionKind::ReadOnlyData,
    );

    let fmt_bytes = b"Factorial: %d\n\0";
    let fmt_offset = asm.emit_bytes(fmt_bytes);
    let fmt_sym = asm.add_symbol(
        b"fmt",
        fmt_offset,
        fmt_bytes.len() as u64,
        SymbolKind::Data,
        SymbolScope::Compilation,
    );

    let n: u64 = 5;
    let n_off = asm.emit_bytes(n);
    let n_sym = asm.add_symbol(
        b"n",
        n_off,
        8,
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

    // Load n into t0 (counter)
    asm.emit_pcrel_load_addr(Reg::T0, n_sym);
    asm.emit_bytes(rv64::encode_ld(Reg::T0, Reg::T0, 0));

    // result in t1 = 1
    asm.emit_bytes(I::ADDI { d: Reg::T1, s: Reg::ZERO, im: 1 });

    let loop_lbl = asm.new_label(b".loop");

    // if t0 <= 1, break
    asm.emit_branch_to(
        I::BLE { s1: Reg::T0, s2: Reg::X1, im: 0 },
        loop_lbl,
    );

    // result *= t0
    asm.emit_bytes(R::MUL { d: Reg::T1, s1: Reg::T1, s2: Reg::T0 });

    // t0 -= 1
    asm.emit_bytes(I::ADDI { d: Reg::T0, s: Reg::T0, im: -1 });

    // loop
    asm.emit_branch_to(
        I::BNE { s1: Reg::T0, s2: Reg::ZERO, im: 0 },
        loop_lbl,
    );

    // printf(fmt, result)
    asm.emit_pcrel_load_addr(Reg::A0, fmt_sym);
    asm.emit_bytes(I::ADDI { d: Reg::A1, s: Reg::T1, im: 0 });
    asm.emit_call_plt(printf_sym);

    asm.emit_function_epilogue();
    asm.emit_return_imm(0);

    asm.add_symbol(
        b"main",
        0,
        asm.section(text_section).data().len() as u64,
        SymbolKind::Text,
        SymbolScope::Dynamic,
    );

    asm.finish()
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
