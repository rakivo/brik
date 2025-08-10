//! Object file builder

use crate::util::rv64;
use crate::asm_riscv::{I, Reg};
use crate::util::into_bytes::IntoBytes;
use crate::reloc::{Reloc, PcrelPart, RelocKind};
use crate::util::attr_builder::RiscvAttrsBuilder;
use crate::object::{
    Endianness,
    SymbolKind,
    SymbolFlags,
    SymbolScope,
    SectionKind,
    Architecture,
    BinaryFormat,
};
use crate::object::write::{
    Symbol,
    Object,
    SymbolId,
    FileFlags,
    SectionId,
    Relocation,
    SymbolSection,
    RelocationFlags,
    StandardSegment,
};

use std::mem;
use std::ops::{Deref, DerefMut};

#[derive(Copy, Clone)]
pub struct Label {
    sym: SymbolId,
}

/// Object file builder
#[derive(Debug)]
pub struct Assembler<'a> {
    obj: Object<'a>,
    pcrel_counter: u32,
    relocs: Vec<(SectionId, Reloc)>,
    curr_section: Option<SectionId>,
}

impl<'a> Deref for Assembler<'a> {
    type Target = Object<'a>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.obj
    }
}

impl<'a> DerefMut for Assembler<'a> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.obj
    }
}

impl<'a> Assembler<'a> {
    const RELOC_PREALLOCATION_COUNT: usize = 4;

    pub fn new(
        format: BinaryFormat,
        arch: Architecture,
        endian: Endianness,
        isa: &str
    ) -> Self {
        let mut asm = Self {
            pcrel_counter: 0,
            curr_section: None,
            obj: Object::new(format, arch, endian),
            relocs: Vec::with_capacity(
                Self::RELOC_PREALLOCATION_COUNT
            ),
        };

        let _attr_section = asm.add_section_at_end(
            StandardSegment::Data,
            b".riscv.attributes",
            SectionKind::Other,
        );

        let attrs = RiscvAttrsBuilder::new("riscv")
            .arch(isa)
            .build();

        asm.emit_bytes(attrs);

        asm
    }

    #[inline(always)]
    pub const fn position_at_end(&mut self, section: SectionId) {
        self.curr_section = Some(section)
    }

    #[must_use]
    #[inline(always)]
    pub const fn curr_section(&self) -> Option<SectionId> {
        self.curr_section
    }

    #[must_use]
    #[track_caller]
    #[inline(always)]
    pub const fn expect_curr_section(&self) -> SectionId {
        self.curr_section.expect("no current section set")
    }

    #[inline(always)]
    pub const fn set_object_flags(&mut self, flags: FileFlags) {
        self.obj.flags = flags
    }

    #[inline(always)]
    pub fn section_size(&self, section_id: SectionId) -> usize {
        self.obj.section(section_id).data().len()
    }

    #[must_use]
    #[inline(always)]
    pub fn finish(mut self) -> Object<'a> {
        self.resolve_local_relocs();
        self.resolve_final_relocs();
        self.obj
    }

    #[inline(always)]
    pub fn next_pcrel_label(
        &mut self,
        part: PcrelPart
    ) -> String {
        format!{
            ".Lpcrel_{p}{lbl}",
            p = match part {
                PcrelPart::Hi20  => "hi20",
                PcrelPart::Lo12I => "lo12i",
                PcrelPart::Lo12S => "lo12s",
            },
            lbl = self.pcrel_counter
        }
    }

    #[inline]
    pub fn new_label(&mut self, name: &[u8]) -> Label {
        let section_id = self.expect_curr_section();
        let offset = self.section_size(section_id) as _;
        let sym = self.add_symbol(
            name,
            offset,
            0,
            SymbolKind::Text,
            SymbolScope::Compilation
        );

        Label { sym }
    }

    #[inline]
    pub fn add_section_at_end(
        &mut self,
        segment: StandardSegment,
        name: &[u8],
        kind: SectionKind,
    ) -> SectionId {
        let section = self.obj.add_section(
            self.obj.segment_name(segment).to_vec(),
            name.to_vec(),
            kind,
        );

        self.position_at_end(section);
        section
    }

    #[inline]
    #[track_caller]
    pub fn add_reloc(
        &mut self,
        section: SectionId,
        reloc: Reloc,
    ) {
        let Reloc {
            offset,
            symbol,
            addend,
            rtype
        } = reloc;

        self.obj.add_relocation(
            section,
            Relocation {
                offset,
                symbol,
                addend,
                flags: RelocationFlags::Elf {
                    r_type: rtype.code()
                }
            },
        ).expect("failed to add relocation")
    }

    #[inline]
    pub fn resolve_final_relocs(&mut self) {
        let relocs = mem::take(&mut self.relocs);

        for (section_id, reloc) in relocs {
            self.add_reloc(section_id, reloc);
        }
    }

    pub fn resolve_local_relocs(&mut self) {
        fn apply_reloc(data: &mut [u8], rtype: RelocKind, delta: i64) {
            match rtype {
                RelocKind::Branch => {
                    if !(-4096..=4094).contains(&delta) || delta % 2 != 0 {
                        panic!("Branch offset out of range: {delta}");
                    }

                    let imm12 = (delta / 2) as i32;
                    let mut inst = u32::from_le_bytes(
                        data.try_into().expect("invalid instruction length")
                    );

                    // clear imm fields: bit31, 30:25, 11:8, bit7
                    inst &= !((1u32 << 31) | (0x3fu32 << 25) | (0xfu32 << 8) | (1u32 << 7));

                    // imm[12]   -> bit  31
                    // imm[10:5] -> bits 30:25
                    // imm[4:1]  -> bits 11:8
                    // imm[11]   -> bit   7

                    // set imm bits
                    inst |= (((imm12 >> 12) & 0x01) as u32) << 31;
                    inst |= (((imm12 >>  5) & 0x3f) as u32) << 25;
                    inst |= (((imm12 >>  1) & 0xf)  as u32) <<  8;
                    inst |= (((imm12 >> 11) & 0x01) as u32) <<  7;

                    inst.copy_into(data);
                }

                RelocKind::Call | RelocKind::CallPlt => {
                    if !(-1 << 31..1 << 31).contains(&delta) {
                        panic!("CALL offset out of range: {delta}");
                    }

                    let imm20 = ((delta + 0x800) >> 12) as i32; // AUIPC imm
                    let imm12 = delta as i32 & 0xfff;           // JALR  imm

                    let mut inst = u32::from_le_bytes(
                        data.try_into().expect("invalid instruction length")
                    );
                    inst &= !(0xfffff000); // clear AUIPC imm[31:12]
                    inst |= (imm20 as u32) << 12;

                    // NOTE: JALR is in the next 4 bytes; need to handle both
                    // this assumes data slice includes AUIPC + JALR (8 bytes)
                    let jalr_slice = &mut data[4..8];
                    let mut jalr_inst = u32::from_le_bytes(
                        jalr_slice.try_into().expect("invalid instruction length")
                    );

                    jalr_inst &= !(0xfff << 20); // clear JALR imm[11:0]
                    jalr_inst |= (imm12 as u32) << 20;

                    data[0..4].copy_from_slice(&inst.to_le_bytes());
                    data[4..8].copy_from_slice(&jalr_inst.to_le_bytes());
                }

                RelocKind::PcrelHi20 => {
                    if !(-1 << 31..1 << 31).contains(&delta) {
                        panic!("PCREL_HI20 offset out of range: {delta}");
                    }

                    // add 0x800 for rounding
                    let imm20 = ((delta + 0x800) >> 12) as i32;
                    let mut inst = u32::from_le_bytes(
                        data.try_into().expect("invalid instruction length")
                    );

                    inst &= !(0xfffff000); // clear imm[31:12].
                    inst |= (imm20 as u32) << 12;

                    inst.copy_into(data);
                }

                RelocKind::PcrelLo12I => {
                    if !(-2048..2048).contains(&delta) {
                        panic!("PCREL_LO12_I offset out of range: {delta}");
                    }

                    let imm12 = delta as i32;
                    let mut inst = u32::from_le_bytes(
                        data.try_into().expect("invalid instruction length")
                    );

                    inst &= !(0xfff << 20); // clear imm[11:0].
                    inst |= (imm12 as u32) << 20;

                    inst.copy_into(data);
                }
            }
        }

        let relocs = std::mem::take(&mut self.relocs);

        let mut new_relocs = Vec::with_capacity(
            Self::RELOC_PREALLOCATION_COUNT
        );

        for (section_id, reloc) in relocs {
            let sym = self.obj.symbol(reloc.symbol);

            // skip if not local or if not the same section
            if sym.scope != SymbolScope::Compilation { continue }
            if !matches!{
                sym.section,
                SymbolSection::Section(sid) if sid == section_id
            } {
                new_relocs.push((section_id, reloc));
                continue
            }

            let delta = sym.value as i64 + reloc.addend - reloc.offset as i64;
            let data = self.obj.section_mut(section_id).data_mut();
            let slice = &mut data[reloc.offset as usize..reloc.offset as usize + 4];

            apply_reloc(slice, reloc.rtype, delta);
        }

        self.relocs = new_relocs;
    }

    #[inline(always)]
    pub fn emit_branch_to(&mut self, i: asm_riscv::I, label: Label) {
        let section_id = self.expect_curr_section();
        let offset = self.emit_bytes_with_reloc(
            i,
            (label.sym, RelocKind::Branch)
        );
        self.relocs.push((
            section_id,
            Reloc {
                offset,
                symbol: label.sym,
                rtype: RelocKind::Branch,
                addend: 0,
            },
        ));
    }

    #[inline]
    pub fn add_symbol_at(
        &mut self,
        name: &[u8],
        value: u64,
        size: u64,
        kind: SymbolKind,
        scope: SymbolScope,
        section: SymbolSection,
    ) -> SymbolId {
        self.obj.add_symbol(Symbol {
            name: name.to_vec(),
            value,
            size,
            kind,
            scope,
            weak: false,
            section,
            flags: SymbolFlags::None,
        })
    }

    #[inline]
    #[track_caller]
    pub fn add_symbol(
        &mut self,
        name: &[u8],
        value: u64,
        size: u64,
        kind: SymbolKind,
        scope: SymbolScope,
    ) -> SymbolId {
        let section = self.expect_curr_section();
        self.obj.add_symbol(Symbol {
            name: name.to_vec(),
            value,
            size,
            kind,
            scope,
            weak: false,
            section: SymbolSection::Section(section),
            flags: SymbolFlags::None,
        })
    }

    #[inline]
    pub fn add_symbol_extern(
        &mut self,
        name: &[u8],
        kind: SymbolKind,
        scope: SymbolScope,
    ) -> SymbolId {
        self.obj.add_symbol(Symbol {
            name: name.to_vec(),
            value: 0,
            size: 0,
            kind,
            scope,
            weak: false,
            section: SymbolSection::Undefined,
            flags: SymbolFlags::None,
        })
    }

    #[inline]
    fn emit_bytes_at_(
        &mut self,
        data: impl IntoBytes<'a>,
        section: SectionId,
        reloc: Option<(SymbolId, RelocKind)>,
    ) -> u64 {
        let offset = self.obj.append_section_data(
            section,
            &data.into_bytes(),
            1 // align
        );

        if let Some((symbol, rtype)) = reloc {
            self.add_reloc(section, Reloc {
                offset,
                symbol,
                rtype,
                addend: 0
            })
        }

        offset
    }

    #[inline(always)]
    pub fn emit_bytes_at(
        &mut self,
        data: impl IntoBytes<'a>,
        section: SectionId,
    ) -> u64 {
        self.obj.append_section_data(
            section,
            &data.into_bytes(),
            1, // align
        )
    }

    #[inline(always)]
    pub fn emit_bytes(&mut self, data: impl IntoBytes<'a>) -> u64 {
        let section = self.expect_curr_section();
        self.emit_bytes_at(data, section)
    }

    #[inline(always)]
    pub fn emit_bytes_with_reloc_at(
        &mut self,
        data: impl IntoBytes<'a>,
        section: SectionId,
        reloc: (SymbolId, RelocKind),
    ) -> u64 {
        self.emit_bytes_at_(data, section, Some(reloc))
    }

    #[inline(always)]
    pub fn emit_bytes_with_reloc(
        &mut self,
        data: impl IntoBytes<'a>,
        reloc: (SymbolId, RelocKind)
    ) -> u64 {
        let section = self.expect_curr_section();
        self.emit_bytes_with_reloc_at(data, section, reloc)
    }

    #[inline]
    pub fn create_pcrel_hi_label_at(
        &mut self,
        section: SectionId,
        offset: u64,
    ) -> SymbolId {
        let name = self.next_pcrel_label(PcrelPart::Hi20);
        self.add_symbol_at(
            name.as_bytes(),
            offset,
            0,
            SymbolKind::Label,
            SymbolScope::Compilation,
            SymbolSection::Section(section),
        )
    }

    #[inline(always)]
    pub fn create_pcrel_hi_label(&mut self, offset: u64) -> SymbolId {
        let section = self.expect_curr_section();
        self.create_pcrel_hi_label_at(section, offset)
    }

    #[inline]
    pub fn emit_pcrel_load_addr_at(
        &mut self,
        section: SectionId,
        rd: Reg,
        target_sym: SymbolId,
    ) {
        let hi_offset = self.emit_bytes_with_reloc_at(
            I::AUIPC { d: rd, im: 0 },
            section,
            (target_sym, RelocKind::PcrelHi20),
        );
        let label = self.create_pcrel_hi_label_at(section, hi_offset);
        self.emit_bytes_with_reloc_at(
            I::ADDI { d: rd, s: rd, im: 0 },
            section,
            (label, RelocKind::PcrelLo12I),
        );
    }

    #[inline(always)]
    pub fn emit_pcrel_load_addr(&mut self, rd: Reg, target_sym: SymbolId) {
        let section = self.expect_curr_section();
        self.emit_pcrel_load_addr_at(section, rd, target_sym);
    }

    #[inline]
    pub fn emit_call_plt_at(
        &mut self,
        section: SectionId,
        target_sym: SymbolId,
    ) {
        self.emit_bytes_with_reloc_at(
            I::AUIPC { d: Reg::T0, im: 0 },
            section,
            (target_sym, RelocKind::CallPlt),
        );
        self.emit_bytes_at(
            I::JALR { d: Reg::RA, s: Reg::T0, im: 0 },
            section,
        );
    }

    #[inline]
    pub fn emit_call_plt(&mut self, target_sym: SymbolId) {
        let section = self.expect_curr_section();
        self.emit_call_plt_at(section, target_sym);
    }

    #[inline]
    pub fn emit_call_direct_at(&mut self, sym: SymbolId, section: SectionId) {
        self.emit_bytes_with_reloc_at(
            I::AUIPC { d: Reg::T0, im: 0 },
            section,
            (sym, RelocKind::Call),
        );
        self.emit_bytes_at(
            I::JALR { d: Reg::RA, s: Reg::T0, im: 0 },
            section,
        );
    }

    #[inline]
    pub fn emit_call_direct(&mut self, sym: SymbolId) {
        let section = self.expect_curr_section();
        self.emit_call_direct_at(sym, section);
    }

    #[inline]
    pub fn emit_function_prologue_at(&mut self, section: SectionId) {
        self.emit_bytes_at(
            I::ADDI { d: Reg::SP, s: Reg::SP, im: -16 },
            section,
        );
        self.emit_bytes_at(rv64::encode_sd(Reg::RA, Reg::SP, 8), section);
        self.emit_bytes_at(rv64::encode_sd(Reg::S0, Reg::SP, 0), section);
        self.emit_bytes_at(
            I::ADDI { d: Reg::S0, s: Reg::SP, im: 16 },
            section
        );
    }

    #[inline(always)]
    pub fn emit_function_prologue(&mut self) {
        let section = self.expect_curr_section();
        self.emit_function_prologue_at(section);
    }

    #[inline]
    pub fn emit_function_epilogue_at(&mut self, section: SectionId) {
        self.emit_bytes_at(rv64::encode_ld(Reg::RA, Reg::SP, 8), section);
        self.emit_bytes_at(rv64::encode_ld(Reg::S0, Reg::SP, 0), section);
        self.emit_bytes_at(
            I::ADDI { d: Reg::SP, s: Reg::SP, im: 16 },
            section,
        );
    }

    #[inline(always)]
    pub fn emit_function_epilogue(&mut self) {
        let section = self.expect_curr_section();
        self.emit_function_epilogue_at(section);
    }

    #[inline(always)]
    pub fn emit_return_imm_at(&mut self, section: SectionId, imm: i64) {
        let bytes = rv64::encode_li_rv64_little(Reg::A0, imm);
        self.emit_bytes_at(bytes, section);
        self.emit_bytes_at(
            I::JALR { d: Reg::ZERO, s: Reg::RA, im: 0 },
            section
        );
    }

    #[inline(always)]
    pub fn emit_return_imm(&mut self, imm: i64) {
        let section = self.expect_curr_section();
        self.emit_return_imm_at(section, imm);
    }
}

