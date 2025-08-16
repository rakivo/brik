use brik::rv32::Reg;
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
    SectionId,
    FileFlags
};

use std::{fs, env, error};

// Custom prologue: call printf with "Entering function"
fn debug_prologue(asm: &mut Assembler, section: SectionId) -> u64 {
    let fmt_sym = asm.symbol_id(b"prologue_msg").unwrap();
    let printf_sym = asm.symbol_id(b"printf").unwrap();

    asm.emit_default_function_prologue_at(section);
    asm.emit_pcrel_load_addr(Reg::A0, fmt_sym);
    asm.emit_call_plt(printf_sym)
}

// Custom epilogue: call printf with "Exiting function"
fn debug_epilogue(asm: &mut Assembler, section: SectionId) -> u64 {
    let fmt_sym = asm.symbol_id(b"epilogue_msg").unwrap();
    let printf_sym = asm.symbol_id(b"printf").unwrap();

    asm.emit_pcrel_load_addr(Reg::A0, fmt_sym);
    asm.emit_call_plt(printf_sym);
    asm.emit_default_function_epilogue_at(section)
}

fn produce_custom_obj<'a>() -> Object<'a> {
    let mut asm = Assembler::new(
        BinaryFormat::Elf,
        Arch::Riscv64,
        Endianness::Little,
        "rv64gc"
    );

    asm.set_custom_emit_function_epilogue(debug_epilogue);
    asm.set_custom_emit_function_prologue(debug_prologue);

    asm.set_object_flags(FileFlags::Elf {
        os_abi: 0,
        abi_version: 0,
        e_flags: 0x4,
    });

    let _rodata = asm.add_rodata_section_at_end();

    let _prologue_msg = asm.define_data("prologue_msg", "Entering function\n\0");
    let inside_msg    = asm.define_data("inside_msg",   "Inside of the function\n\0");
    let _epilogue_msg = asm.define_data("epilogue_msg", "Exiting function\n\0");

    let printf_sym = asm.add_symbol_extern(
        "printf",
        SymbolKind::Text,
        SymbolScope::Dynamic
    );

    let _text = asm.add_text_section_at_end();

    asm.emit_function_prologue();
    asm.emit_pcrel_load_addr(Reg::A0, inside_msg);
    asm.emit_call_plt(printf_sym);
    asm.emit_function_epilogue();
    asm.emit_return_imm(0);

    asm.add_symbol(
        b"main",
        0,
        asm.curr_offset(),
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

    let obj = produce_custom_obj();
    let file = fs::File::create(output_path)?;
    obj.write_stream(&file)?;

    println!("[wrote object file to {output_path}]");
    Ok(())
}

