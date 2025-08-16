//! Object file builder

use crate::util::misc;
use crate::rv32::AqRl;
use crate::rv64::I64::*;
use crate::rv32::Reg::{self, *};
use crate::rv32::I32::{self, *};
use crate::misc_enc::{leb128, pseudo};
use crate::util::into_bytes::IntoBytes;
use crate::asm::label::{Label, LabelId};
use crate::asm::arch::{Arch, AddressSize};
use crate::util::compat_fn::CompatFnWrapper;
use crate::util::attr_builder::RiscvAttrsBuilder;
use crate::asm::reloc::{Reloc, PcrelPart, RelocKind};
use crate::asm::errors::{
    FinishError,
    UnplacedLabelInfo
};
use crate::object::{
    Endianness,
    SymbolKind,
    SymbolFlags,
    SymbolScope,
    SectionKind,
    BinaryFormat,
};
use crate::object::write::{
    Symbol,
    Object,
    Comdat,
    ComdatId,
    SymbolId,
    FileFlags,
    SectionId,
    ComdatKind,
    Relocation,
    SectionFlags,
    SymbolSection,
    RelocationFlags,
    StandardSegment,
};

use std::str;
use std::vec;
use std::format;
use std::vec::Vec;
use std::string::String;
use std::borrow::ToOwned;

use core::{mem, panic};
use core::ops::{Deref, DerefMut};

use rustc_hash::FxHashMap;
use num_traits::{
    Signed,
    PrimInt,
    Unsigned,
    ToPrimitive,
    FromPrimitive,
};

pub type EmitFunctionPrologue = fn(&mut Assembler<'_>, SectionId) -> u64;
pub type EmitFunctionEpilogue = fn(&mut Assembler<'_>, SectionId) -> u64;

#[inline(always)]
fn default_emit_function_prologue(
    asm: &mut Assembler<'_>,
    section: SectionId
) -> u64 {
    let ptr_size = asm.address_bytes() as i16;

    asm.emit_addi_at(section, SP, SP, -ptr_size * 2);
    asm.emit_sd_at(section,   RA, SP, ptr_size);
    asm.emit_sd_at(section,   S0, SP, 0);
    asm.emit_addi_at(section, S0, SP, ptr_size * 2)
}

#[inline(always)]
fn default_emit_function_epilogue(
    asm: &mut Assembler<'_>,
    section: SectionId
) -> u64 {
    let ptr_size = asm.address_bytes() as i16;

    asm.emit_ld_at(section,   RA, SP, ptr_size);
    asm.emit_ld_at(section,   S0, SP, 0);
    asm.emit_addi_at(section, SP, SP, ptr_size * 2)
}

/// Object file builder
#[derive(Debug)]
pub struct Assembler<'a> {
    obj: Object<'a>,

    arch: Arch,

    relocs: Vec<(SectionId, Reloc)>,

    curr_section: Option<SectionId>,

    pcrel_counter: u32,
    lbl_id_counter: LabelId,

    format: BinaryFormat,

    labels: FxHashMap<LabelId, Label>,
    pub(crate) unplaced_labels: FxHashMap<LabelId, UnplacedLabelInfo>,

    custom_emit_function_prologue: CompatFnWrapper<EmitFunctionPrologue>,
    custom_emit_function_epilogue: CompatFnWrapper<EmitFunctionEpilogue>,
}

impl<'a> Deref for Assembler<'a> {
    type Target = Object<'a>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.obj }
}

impl<'a> DerefMut for Assembler<'a> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.obj }
}

impl<'a> Assembler<'a> {
    const RELOC_PREALLOCATION_COUNT: usize = 4;

    /// Create a new `Assembler` instance.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brik::asm::Assembler;
    /// use brik::asm::arch::Arch;
    /// use brik::object::{BinaryFormat, Endianness};
    ///
    /// let mut asm = Assembler::new(
    ///     BinaryFormat::Elf,
    ///     Arch::Riscv64,
    ///     Endianness::Little,
    ///     "rv64gc",
    /// );
    /// ```
    pub fn new(
        format: BinaryFormat,
        arch: Arch,
        endian: Endianness,
        isa: &str
    ) -> Self {
        let mut asm = Self {
            format,

            arch,

            curr_section: None,

            pcrel_counter: 0,
            lbl_id_counter: LabelId(0),

            labels: FxHashMap::default(),
            unplaced_labels: FxHashMap::default(),

            obj: Object::new(
                format,
                arch.into_object_architecture(),
                endian
            ),

            relocs: Vec::with_capacity(
                Self::RELOC_PREALLOCATION_COUNT
            ),

            custom_emit_function_prologue: CompatFnWrapper(default_emit_function_prologue),
            custom_emit_function_epilogue: CompatFnWrapper(default_emit_function_epilogue),
        };

        if asm.format == BinaryFormat::Elf {
            let riscv_attrs = asm.add_section(
                StandardSegment::Data,
                b".riscv.attributes",
                SectionKind::Other,
            );

            let attrs = RiscvAttrsBuilder::new("riscv")
                .arch(isa)
                .build();

            asm.emit_bytes_at(riscv_attrs, attrs);
        }

        asm
    }

    /// Finishes object emission
    #[inline]
    pub fn finish(mut self) -> Result<Object<'a>, FinishError> {
        if self.unplaced_labels.is_empty() {
            self.resolve_local_relocs();
            self.resolve_final_relocs();
            return Ok(self.obj)
        }

        Err(FinishError::from_asm(self))
    }

    /// Sets current section to `section`
    #[inline(always)]
    pub fn position_at_end(&mut self, section: SectionId) {
        self.curr_section = Some(section)
    }

    #[inline(always)]
    pub fn set_object_flags(&mut self, flags: FileFlags) {
        self.obj.flags = flags
    }

    #[inline(always)]
    pub fn set_custom_emit_function_prologue(&mut self, f: EmitFunctionPrologue) {
        self.custom_emit_function_prologue = CompatFnWrapper(f)
    }

    #[inline(always)]
    pub fn set_custom_emit_function_epilogue(&mut self, f: EmitFunctionEpilogue) {
        self.custom_emit_function_epilogue = CompatFnWrapper(f)
    }

    #[inline(always)]
    pub const fn arch(&self) -> Arch {
        self.arch
    }

    #[inline(always)]
    pub const fn address_size(&self) -> AddressSize {
        self.arch().address_size()
    }

    #[inline(always)]
    pub const fn address_bytes(&self) -> u8 {
        self.arch().address_size().bytes()
    }

    #[inline(always)]
    pub const fn address_bits(&self) -> u8 {
        self.arch().address_size().bits()
    }

    #[must_use]
    #[inline(always)]
    pub fn curr_offset(&self) -> u64 {
        let sid = self.expect_curr_section();
        self.section_size(sid)
    }

    // ----- DATA/PADDING EMISSION HELPERS -----

    with_no_at! {
        emit_byte,
        #[inline(always)]
        pub fn emit_byte_at(
            &mut self,
            section: SectionId,
            v: u8
        ) -> u64 { self.emit_bytes_at(section, v) }
    }

    with_no_at! {
        emit_half,
        #[inline(always)]
        pub fn emit_half_at(
            &mut self,
            section: SectionId,
            v: u16
        ) -> u64 { self.emit_bytes_at(section, v) }
    }

    with_no_at! {
        emit_word,
        #[inline(always)]
        pub fn emit_word_at(
            &mut self,
            section: SectionId,
            v: u32
        ) -> u64 { self.emit_bytes_at(section, v) }
    }

    with_no_at! {
        emit_dword,
        #[inline(always)]
        pub fn emit_dword_at(
            &mut self,
            section: SectionId,
            v: u64
        ) -> u64 { self.emit_bytes_at(section, v) }
    }

    #[inline(always)]
    pub fn emit_uleb_at<T>(&mut self, section: SectionId, value: T) -> u64
    where
        T: PrimInt + Unsigned + FromPrimitive + ToPrimitive
    {
        let bytes = leb128::encode_uleb128(value);
        self.emit_bytes_at(section, bytes)
    }

    #[inline(always)]
    pub fn emit_uleb<T>(&mut self, value: T) -> u64
    where
        T: PrimInt + Unsigned + FromPrimitive + ToPrimitive
    {
        let section = self.expect_curr_section();
        self.emit_uleb_at(section, value)
    }

    #[inline(always)]
    pub fn emit_sleb_at<T>(&mut self, section: SectionId, value: T) -> u64
    where
        T: PrimInt + Signed + FromPrimitive + ToPrimitive
    {
        let bytes = leb128::encode_sleb128(value);
        self.emit_bytes_at(section, bytes)
    }

    #[inline(always)]
    pub fn emit_sleb<T>(&mut self, value: T) -> u64
    where
        T: PrimInt + Signed + FromPrimitive + ToPrimitive
    {
        let section = self.expect_curr_section();
        self.emit_sleb_at(section, value)
    }

    with_no_at! {
        emit_str,
        #[inline(always)]
        pub fn emit_str_at(
            &mut self,
            section: SectionId,
            s: &'a str
        ) -> u64 { self.emit_bytes_at(section, s.as_bytes()) }
    }

    with_no_at! {
        emit_string,
        #[inline(always)]
        pub fn emit_string_at(
            &mut self,
            section: SectionId,
            s: String
        ) -> u64 { self.emit_bytes_at(section, s.into_bytes()) }
    }

    with_no_at! {
        emit_strz,
        #[inline(always)]
        pub fn emit_strz_at(
            &mut self,
            section: SectionId,
            s: &'a str
        ) -> u64 {
            self.emit_bytes_at(section, s.as_bytes());
            self.emit_byte_at(section, 0)
        }
    }

    with_no_at! {
        emit_stringz,
        #[inline(always)]
        pub fn emit_stringz_at(
            &mut self,
            section: SectionId,
            s: String
        ) -> u64 {
            self.emit_bytes_at(section, s.into_bytes());
            self.emit_byte_at(section, 0)
        }
    }

    with_no_at! {
        emit_zeroes,
        #[inline(always)]
        pub fn emit_zeroes_at(
            &mut self,
            section: SectionId,
            count: usize
        ) -> u64 {
            self.emit_bytes_at(section, vec![0u8; count])
        }
    }

    with_no_at! {
        emit_fill,
        #[inline(always)]
        pub fn emit_fill_at(
            &mut self,
            section: SectionId,
            count: usize,
            value: u8
        ) -> u64 {
            self.emit_bytes_at(section, vec![value; count])
        }
    }

    // ----- RAW INSTRUCTION EMISSION HELPERS -----

    with_no_at! {
        emit_r,
        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub fn emit_r_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            d: Reg,
            funct3: u32,
            s1: Reg,
            s2: Reg,
            funct7: u32
        ) -> u64 {
            self.emit_bytes_at(section, I32::r(opcode, d, funct3, s1, s2, funct7))
        }
    }

    with_no_at! {
        emit_i,
        #[inline(always)]
        pub fn emit_i_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            d: Reg,
            funct3: u32,
            s: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, I32::i(opcode, d, funct3, s, im))
        }
    }

    with_no_at! {
        emit_i7,
        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub fn emit_i7_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            d: Reg,
            funct3: u32,
            s: Reg,
            im: u8,
            funct7: u32
        ) -> u64 {
            self.emit_bytes_at(section, I32::i7(opcode, d, funct3, s, im, funct7))
        }
    }

    with_no_at! {
        emit_s,
        #[inline(always)]
        pub fn emit_s_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            funct3: u32,
            s1: Reg,
            s2: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, I32::s(opcode, funct3, s1, s2, im))
        }
    }

    with_no_at! {
        emit_b,
        #[inline(always)]
        pub fn emit_b_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            funct3: u32,
            s1: Reg,
            s2: Reg,
            im_b: i16
        ) -> u64 {
            self.emit_bytes_at(section, I32::b(opcode, funct3, s1, s2, im_b))
        }
    }

    with_no_at! {
        emit_u,
        #[inline(always)]
        pub fn emit_u_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            d: Reg,
            im: i32
        ) -> u64 {
            self.emit_bytes_at(section, I32::u(opcode, d, im))
        }
    }

    with_no_at! {
        emit_j,
        #[inline(always)]
        pub fn emit_j_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            d: Reg,
            im_j: i32
        ) -> u64 {
            self.emit_bytes_at(section, I32::j(opcode, d, im_j))
        }
    }

    with_no_at! {
        emit_amo,
        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub fn emit_amo_at(
            &mut self,
            section: SectionId,
            opcode: u32,
            rd: Reg,
            funct3: u32,
            rs1: Reg,
            rs2: Reg,
            aqrl: AqRl,
            funct5: u32
        ) -> u64 {
            self.emit_bytes_at(
                section,
                I32::amo(opcode, rd, funct3, rs1, rs2, aqrl, funct5)
            )
        }
    }

    // ----- SECTION MANAGEMENT -----

    #[must_use]
    #[inline(always)]
    pub const fn curr_section(&self) -> Option<SectionId> {
        self.curr_section
    }

    #[must_use]
    #[track_caller]
    #[inline(always)]
    pub fn expect_curr_section(&self) -> SectionId {
        self.curr_section().expect("no current section set")
    }

    #[must_use]
    #[inline(always)]
    pub fn section_size(&self, section_id: SectionId) -> u64 {
        self.obj.section(section_id).data().len() as _
    }

    #[inline(always)]
    pub fn align_to(&mut self, align: u64) {
        let section_id = self.expect_curr_section();
        let size = self.section_size(section_id);
        let pad = (align - (size % align)) % align;
        if pad > 0 {
            self.emit_zeroes(pad as _);
        }
    }

    // --------- COMDAT SECTION MANAGEMENT ----------

    /// Add a new COMDAT section group and return its `ComdatId`.
    #[inline(always)]
    pub fn add_comdat(
        &mut self,
        kind: ComdatKind,
        symbol: SymbolId
    ) -> ComdatId {
        self.obj.add_comdat(Comdat {
            kind,
            symbol,
            sections: Vec::default()
        })
    }

    /// Append section to a COMDAT section group
    #[inline(always)]
    pub fn add_section_to_comdat(
        &mut self,
        section: SectionId,
        comdat_id: ComdatId,
    ) {
        self.obj.comdat_mut(comdat_id).sections.push(section);
    }

    /// Append section to a COMDAT section group
    #[inline(always)]
    pub fn add_section_to_comdat_if_not_added(
        &mut self,
        section: SectionId,
        comdat_id: ComdatId,
    ) -> bool {
        let sections = &mut self.obj.comdat_mut(comdat_id).sections;
        if sections.contains(&section) {
            return true
        }

        sections.push(section);
        false
    }

    /// Get slice of all sections in a COMDAT section group
    #[inline(always)]
    pub fn comdat_sections(&self, comdat_id: ComdatId) -> &[SectionId] {
        &self.obj.comdat(comdat_id).sections
    }

    with_at_end!{
        add_section_and_add_to_comdat_at_end,
        #[inline]
        pub fn add_section_and_add_to_comdat(
            &mut self,
            segment: StandardSegment,
            name: impl AsRef<[u8]>,
            kind: SectionKind,
            comdat_id: ComdatId
        ) -> SectionId {
            let section = self.add_section(segment, name, kind);
            self.add_section_to_comdat(section, comdat_id);
            section
        }
    }

    // -----------------------------------

    with_at_end!{
        add_text_section_at_end,
        /// Add a text section.
        #[inline(always)]
        pub fn add_text_section(&mut self) -> SectionId {
            self.add_section(
                StandardSegment::Text,
                b".text",
                SectionKind::Text,
            )
        }
    }

    with_at_end!{
        add_data_section_at_end,
        /// Add a data section.
        #[inline]
        pub fn add_data_section(&mut self) -> SectionId {
            self.add_section(
                StandardSegment::Data,
                b".data",
                SectionKind::Data
            )
        }
    }

    with_at_end!{
        add_rodata_section_at_end,
        /// Add a read-only data section.
        #[inline]
        pub fn add_rodata_section(&mut self) -> SectionId {
            self.add_section(
                StandardSegment::Data,
                if self.format == BinaryFormat::Coff {
                    b".rdata".as_ref()
                } else {
                    b".rodata".as_ref()
                },
                SectionKind::ReadOnlyData
            )
        }
    }

    with_at_end!{
        add_bss_section_at_end,
        /// Add a BSS section.
        #[inline]
        pub fn add_bss_section(&mut self) -> SectionId {
            self.add_section(
                StandardSegment::Data,
                b".bss",
                SectionKind::UninitializedData
            )
        }
    }

    with_at_end!{
        add_section_at_end,
        /// Add a new section and return its `SectionId`.
        ///
        /// This also creates a section symbol.
        #[inline]
        pub fn add_section(
            &mut self,
            segment: StandardSegment,
            name: impl AsRef<[u8]>,
            kind: SectionKind,
        ) -> SectionId {
            self.obj.add_section(
                self.segment_name(segment).to_vec(),
                name.as_ref().to_vec(),
                kind,
            )
        }
    }

    // --------- SECTION FLAGS MANAGEMENT ---------

    with_at_end!{
        add_section_with_flags_at_end,
        #[inline]
        pub fn add_section_with_flags(
            &mut self,
            segment: StandardSegment,
            name: impl AsRef<[u8]>,
            kind: SectionKind,
            flags: SectionFlags
        ) -> SectionId {
            let section = self.add_section(
                segment,
                name,
                kind
            );

            self.set_section_flags(section, flags);

            section
        }
    }

    #[inline(always)]
    pub fn set_section_flags(
        &mut self,
        section: SectionId,
        flags: SectionFlags
    ) {
        *self.section_flags_mut(section) = flags
    }

    // --------------------------

    #[inline]
    pub fn next_pcrel_label(
        &mut self,
        part: PcrelPart
    ) -> String {
        let l = format!{
            ".Lpcrel_{p}{lbl}",
            p = match part {
                PcrelPart::Hi20  => "hi20",
                PcrelPart::Lo12I => "lo12i",
                PcrelPart::Lo12S => "lo12s",
            },
            lbl = self.pcrel_counter
        };

        self.pcrel_counter += 1;
        l
    }

    #[must_use]
    #[inline(always)]
    pub fn next_brik_lbl_id(&mut self) -> LabelId {
        let id = self.lbl_id_counter;
        self.lbl_id_counter.0 += 1;
        id
    }

    #[inline]
    fn add_label_(&mut self, name: impl AsRef<[u8]>, offset: u64) -> Label {
        let sym = self.add_symbol(
            name,
            offset,
            0,
            SymbolKind::Text,
            SymbolScope::Compilation,
            false,
            SymbolFlags::None
        );

        Label { sym }
    }

    #[inline]
    pub fn add_label_here(&mut self, name: impl AsRef<[u8]>) -> LabelId {
        let curr_offset = self.curr_offset();
        let l = self.add_label_(name, curr_offset);
        let id = self.next_brik_lbl_id();
        self.labels.insert(id, l);
        id
    }

    #[inline]
    #[track_caller]
    pub fn declare_label(&mut self, name: impl AsRef<[u8]>) -> LabelId {
        let l = self.add_label_(name, 0);
        let id = self.next_brik_lbl_id();
        self.labels.insert(id, l);

        self.unplaced_labels.insert(id, UnplacedLabelInfo {
            caller_loc: panic::Location::caller()
        });

        id
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

    // TODO(#23): Make `resolve_local_relocs` work for 32-bit architectures
    pub fn resolve_local_relocs(&mut self) {
        debug_assert_eq!{
            self.arch,
            Arch::Riscv64,
            "only 64-bit architectures are supported for now"
        };

        fn apply_reloc(data: &mut [u8], rtype: RelocKind, delta: i64) {
            match rtype {
                RelocKind::Branch => {
                    if !(-4096..=4094).contains(&delta) || delta % 2 != 0 {
                        panic!("Branch offset out of range: {delta}");
                    }

                    let imm13 = delta as i32;
                    let mut inst = misc::le_bytes_into_int::<u32>(data);

                    // clear imm fields: bit31, 30:25, 11:8, bit7
                    inst &= !((1u32 << 31) | (0x3fu32 << 25) | (0xfu32 << 8) | (1u32 << 7));

                    inst |= (((imm13 >> 12) & 0x01) as u32) << 31;
                    inst |= (((imm13 >>  5) & 0x3f) as u32) << 25;
                    inst |= (((imm13 >>  1) & 0xf)  as u32) <<  8;
                    inst |= (((imm13 >> 11) & 0x01) as u32) <<  7;

                    inst.copy_into(data);
                }

                RelocKind::Jal => {
                    if !(-1048576..=1048574).contains(&delta) || delta % 2 != 0 {
                        panic!("JAL offset out of range: {delta}");
                    }

                    let imm21 = delta as i32;
                    let mut inst = misc::le_bytes_into_int::<u32>(data);

                    // clear the imm field (bits 31:12)
                    inst &= 0x00000fff;

                    inst |= (((imm21 >> 20) & 0x001) as u32) << 31; // imm[20]    -> bit 31
                    inst |= (((imm21 >> 1)  & 0x3ff) as u32) << 21; // imm[10:1]  -> bits 30:21
                    inst |= (((imm21 >> 11) & 0x001) as u32) << 20; // imm[11]    -> bit 20
                    inst |= (((imm21 >> 12) & 0x0ff) as u32) << 12; // imm[19:12] -> bits 19:12

                    data.copy_from_slice(&inst.to_le_bytes());
                }

                RelocKind::Call | RelocKind::CallPlt => {
                    if !(-1 << 31..1 << 31).contains(&delta) {
                        panic!("CALL offset out of range: {delta}");
                    }

                    let imm20 = ((delta + 0x800) >> 12) as i32; // AUIPC imm
                    let imm12 = delta as i32 & 0xfff;           // JALR  imm

                    let mut inst = misc::le_bytes_into_int::<u32>(&data[0..4]);
                    inst &= !0xfffff000; // clear AUIPC imm[31:12]
                    inst |= (imm20 as u32) << 12;

                    // NOTE: JALR is in the next 4 bytes; need to handle both
                    // this assumes data slice includes AUIPC + JALR (8 bytes)
                    let jalr_slice = &mut data[4..8];
                    let mut jalr_inst = misc::le_bytes_into_int::<u32>(jalr_slice);

                    jalr_inst &= !(0xfff << 20); // clear JALR imm[11:0]
                    jalr_inst |= (imm12 as u32) << 20;

                    inst.copy_into(&mut data[0..4]);
                    jalr_inst.copy_into(&mut data[4..8]);
                }

                RelocKind::PcrelHi20 => {
                    if !(-1 << 31..1 << 31).contains(&delta) {
                        panic!("PCREL_HI20 offset out of range: {delta}");
                    }

                    // add 0x800 for rounding
                    let imm20 = ((delta + 0x800) >> 12) as i32;
                    let mut inst = misc::le_bytes_into_int::<u32>(data);

                    inst &= !0xfffff000; // clear imm[31:12].
                    inst |= (imm20 as u32) << 12;

                    inst.copy_into(data);
                }

                RelocKind::PcrelLo12I => {
                    if !(-2048..2048).contains(&delta) {
                        panic!("PCREL_LO12_I offset out of range: {delta}");
                    }

                    let imm12 = delta as i32;
                    let mut inst = misc::le_bytes_into_int::<u32>(data);

                    inst &= !(0xfff << 20); // clear imm[11:0].
                    inst |= (imm12 as u32) << 20;

                    inst.copy_into(data);
                }
            }
        }

        let relocs = mem::take(&mut self.relocs);

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

    with_no_at!{
        emit_branch_to,
        #[inline(always)]
        pub fn emit_branch_to_at(
            &mut self,
            section: SectionId,
            lbl_id: LabelId,
            i: I32
        ) -> u64 {
            let rtype = match i {
                JAL { .. } => RelocKind::Jal,
                BEQ { .. }  | BNE { .. } |
                BLT { .. }  | BGE { .. } |
                BLTU { .. } | BGEU { .. } => RelocKind::Branch,
                _ => unimplemented!("unsupported branch instruction type"),
            };

            let offset = self.emit_bytes(i);

            self.relocs.push((
                section,
                Reloc {
                    offset,
                    symbol: self.get_label(lbl_id).sym,
                    rtype,
                    addend: 0,
                }
            ));

            offset
        }
    }

    #[must_use]
    #[inline(always)]
    pub fn get_symbol_name(&self, sym: SymbolId) -> &[u8] {
        &self.symbol(sym).name
    }

    #[must_use]
    #[inline(always)]
    pub fn get_label(&self, lbl_id: LabelId) -> &Label {
        &self.labels[&lbl_id]
    }

    #[must_use]
    #[inline(always)]
    pub fn get_label_mut(&mut self, lbl_id: LabelId) -> &mut Label {
        self.labels.get_mut(&lbl_id).unwrap()
    }

    #[inline]
    pub fn place_label_at(&mut self, lbl_id: LabelId, offset: u64) {
        let label = self.get_label(lbl_id);
        let sym = &mut self.obj.symbol_mut(label.sym);
        sym.value = offset;
        _ = self.unplaced_labels.remove(&lbl_id)
    }

    #[inline]
    pub fn place_label_here(&mut self, lbl_id: LabelId) {
        let section_id = self.expect_curr_section();
        let offset = self.section_size(section_id);
        self.place_label_at(lbl_id, offset);
    }

    #[inline]
    pub fn add_comm_symbol_at(
        &mut self,
        section: SymbolSection,
        name: impl AsRef<[u8]>,
        size: u64,
        align: u64,
        weak: bool
    ) -> SymbolId {
        self.obj.add_common_symbol(
            Symbol {
                name: name.as_ref().to_vec(),
                value: 0,
                size,
                kind: SymbolKind::Data,
                scope: SymbolScope::Linkage,
                weak,
                section,
                flags: SymbolFlags::None
            },
            size,
            align
        )
    }

    #[inline]
    pub fn add_comm_symbol(
        &mut self,
        name: impl AsRef<[u8]>,
        size: u64,
        align: u64,
        weak: bool
    ) -> SymbolId {
        self.add_comm_symbol_at(
            SymbolSection::Common, name, size, align, weak
        )
    }

    #[inline]
    pub fn define_data_at(
        &mut self,
        section: SymbolSection,
        name: impl AsRef<[u8]>,
        data: impl IntoBytes<'a>
    ) -> SymbolId {
        let offset = self.curr_offset();
        let bytes = data.into_bytes();
        let size = bytes.len() as _;
        self.emit_bytes(bytes);
        self.add_symbol_at(
            section,
            name.as_ref(),
            offset,
            size,
            SymbolKind::Data,
            SymbolScope::Compilation,
            false, // strong
            SymbolFlags::None
        )
    }

    #[inline]
    pub fn define_data(
        &mut self,
        name: impl AsRef<[u8]>,
        data: impl IntoBytes<'a>
    ) -> SymbolId {
        let offset = self.curr_offset();
        let bytes = data.into_bytes();
        let size = bytes.len() as _;
        self.emit_bytes(bytes);
        self.add_symbol(
            name.as_ref(),
            offset,
            size,
            SymbolKind::Data,
            SymbolScope::Compilation,
            false, // strong
            SymbolFlags::None
        )
    }

    with_no_at!{
        symbol
        add_symbol,
        #[inline]
        #[allow(clippy::too_many_arguments)]
        pub fn add_symbol_at(
            &mut self,
            section: SymbolSection,
            name: impl AsRef<[u8]>,
            value: u64,
            size: u64,
            kind: SymbolKind,
            scope: SymbolScope,
            weak: bool,
            flags: SymbolFlags<SectionId, SymbolId>
        ) -> SymbolId {
            self.obj.add_symbol(Symbol {
                name: name.as_ref().to_owned(),
                value,
                size,
                kind,
                scope,
                weak,
                section,
                flags
            })
        }
    }

    #[inline]
    fn add_symbol_extern_(
        &mut self,
        name: impl AsRef<[u8]>,
        kind: SymbolKind,
        scope: SymbolScope,
        weak: bool
    ) -> SymbolId {
        self.add_symbol_at(
            SymbolSection::Undefined,
            name,
            0,
            0,
            kind,
            scope,
            weak,
            SymbolFlags::None
        )
    }

    #[inline(always)]
    pub fn add_symbol_extern(
        &mut self,
        name: impl AsRef<[u8]>,
        kind: SymbolKind,
        scope: SymbolScope,
    ) -> SymbolId {
        self.add_symbol_extern_(name, kind, scope, false)
    }

    #[inline(always)]
    pub fn add_symbol_extern_weak(
        &mut self,
        name: impl AsRef<[u8]>,
        kind: SymbolKind,
        scope: SymbolScope,
    ) -> SymbolId {
        self.add_symbol_extern_(name, kind, scope, true)
    }

    with_no_at!{
        symbol
        add_symbol_global,
        #[inline]
        pub fn add_symbol_global_at(
            &mut self,
            section: SymbolSection,
            name: impl AsRef<[u8]>,
            value: u64,
            size: u64,
            kind: SymbolKind,
        ) -> SymbolId {
            self.add_symbol_at(
                section,
                name,
                value,
                size,
                kind,
                SymbolScope::Linkage,
                false, // strong
                SymbolFlags::None
            )
        }
    }

    with_no_at!{
        emit_bytes,
        #[inline(always)]
        pub fn emit_bytes_at(
            &mut self,
            section: SectionId,
            data: impl IntoBytes<'a>,
        ) -> u64 {
            self.obj.append_section_data(
                section,
                &data.into_bytes(),
                1 // align
            )
        }
    }

    with_no_at!{
        emit_bytes_with_reloc,
        #[inline]
        pub fn emit_bytes_with_reloc_at(
            &mut self,
            section: SectionId,
            data: impl IntoBytes<'a>,
            reloc_info: (SymbolId, RelocKind),
        ) -> u64 {
            let offset = self.obj.append_section_data(
                section,
                &data.into_bytes(),
                1 // align
            );

            let (symbol, rtype) = reloc_info;

            self.add_reloc(section, Reloc {
                offset,
                symbol,
                rtype,
                addend: 0
            });

            offset
        }
    }

    with_no_at!{
        create_pcrel_hi_label,
        #[inline]
        pub fn create_pcrel_hi_label_at(
            &mut self,
            section: SectionId,
            offset: u64,
        ) -> SymbolId {
            let name = self.next_pcrel_label(PcrelPart::Hi20);
            self.add_symbol_at(
                SymbolSection::Section(section),
                name.as_bytes(),
                offset,
                0,
                SymbolKind::Label,
                SymbolScope::Compilation,
                false,
                SymbolFlags::None
            )
        }
    }

    with_no_at! {
        emit_function_prologue,
        #[inline(always)]
        pub fn emit_function_prologue_at(&mut self, section: SectionId) -> u64 {
            (self.custom_emit_function_prologue)(self, section)
        }
    }

    with_no_at! {
        emit_default_function_prologue,
        #[inline(always)]
        pub fn emit_default_function_prologue_at(&mut self, section: SectionId) -> u64 {
            default_emit_function_prologue(self, section)
        }
    }

    with_no_at! {
        emit_function_epilogue,
        #[inline(always)]
        pub fn emit_function_epilogue_at(&mut self, section: SectionId) -> u64 {
            (self.custom_emit_function_epilogue)(self, section)
        }
    }

    with_no_at! {
        emit_default_function_epilogue,
        #[inline(always)]
        pub fn emit_default_function_epilogue_at(&mut self, section: SectionId) -> u64 {
            default_emit_function_epilogue(self, section)
        }
    }

    // ----- OPS EMISSION -----

    with_no_at! {
        emit_pcrel_load_addr,
        #[inline]
        pub fn emit_pcrel_load_addr_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            target_sym: SymbolId,
        ) -> u64 {
            let hi_offset = self.emit_bytes_with_reloc_at(
                section,
                AUIPC { d: rd, im: 0 },
                (target_sym, RelocKind::PcrelHi20),
            );
            let label = self.create_pcrel_hi_label_at(section, hi_offset);
            self.emit_bytes_with_reloc_at(
                section,
                ADDI { d: rd, s: rd, im: 0 },
                (label, RelocKind::PcrelLo12I),
            )
        }
    }

    with_no_at! {
        emit_call_plt,
        #[inline]
        pub fn emit_call_plt_at(
            &mut self,
            section: SectionId,
            target_sym: SymbolId,
        ) -> u64 {
            self.emit_bytes_with_reloc_at(
                section,
                AUIPC { d: T0, im: 0 },
                (target_sym, RelocKind::CallPlt),
            );
            self.emit_jalr(RA, T0, 0)
        }
    }

    with_no_at! {
        emit_call_direct,
        #[inline]
        pub fn emit_call_direct_at(
            &mut self,
            section: SectionId,
            sym: SymbolId
        ) -> u64 {
            self.emit_bytes_with_reloc_at(
                section,
                AUIPC { d: T0, im: 0 },
                (sym, RelocKind::Call),
            );
            self.emit_jalr(RA, T0, 0)
        }
    }

    with_no_at! {
        emit_call_label,
        #[inline]
        pub fn emit_call_label_at(
            &mut self,
            section: SectionId,
            label: LabelId,
        ) -> u64 {
            self.emit_call_label_plt_at(
                section,
                label
            )
        }
    }

    with_no_at! {
        emit_call_label_plt,
        #[inline]
        pub fn emit_call_label_plt_at(
            &mut self,
            section: SectionId,
            label: LabelId,
        ) -> u64 {
            let sym = self.get_label(label).sym;
            self.emit_call_plt_at(section, sym)
        }
    }

    with_no_at! {
        emit_call_label_direct,
        #[inline]
        pub fn emit_call_label_direct_at(
            &mut self,
            section: SectionId,
            label: LabelId,
        ) -> u64 {
            let sym = self.get_label(label).sym;
            self.emit_call_direct_at(section, sym)
        }
    }

    with_no_at! {
        emit_return_im32,
        #[inline(always)]
        pub fn emit_ret_im32_at(
            &mut self,
            section: SectionId,
            im: i32
        ) -> u64 {
            self.emit_li32_at(section, A0, im);
            self.emit_ret_at(section)
        }
    }

    with_no_at! {
        emit_return_im64,
        #[inline(always)]
        pub fn emit_ret_im64_at(
            &mut self,
            section: SectionId,
            im: i64
        ) -> u64 {
            self.emit_li64_at(section, A0, im);
            self.emit_ret()
        }
    }

    with_no_at! {
        emit_return_imm,
        #[inline(always)]
        pub fn emit_return_imm_at(
            &mut self,
            section: SectionId,
            imm: i64
        ) -> u64 {
            match self.arch {
                Arch::Riscv32 => self.emit_ret_im32_at(section, imm as i32),
                Arch::Riscv64 => self.emit_ret_im64_at(section, imm),
            }
        }
    }

    // ----- LOAD/STORE OPERATIONS -----

    with_no_at! {
        emit_lb,
        /// Emit load byte (LB)
        #[inline(always)]
        pub fn emit_lb_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, LB { d: rd, s: rs1, im: offset })
        }
    }

    with_no_at! {
        emit_lh,
        /// Emit load halfword (LH)
        #[inline(always)]
        pub fn emit_lh_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, LH { d: rd, s: rs1, im: offset })
        }
    }

    with_no_at! {
        emit_lw,
        /// Emit load word (LW)
        #[inline(always)]
        pub fn emit_lw_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, LW { d: rd, s: rs1, im: offset })
        }
    }

    with_no_at! {
        emit_ld,
        /// Emit load doubleword (LD) - RV64 only
        #[inline(always)]
        pub fn emit_ld_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(
                section,
                LD { d: rd, s: rs1, im: offset }
            )
        }
    }

    with_no_at! {
        emit_sb,
        /// Emit store byte (SB)
        #[inline(always)]
        pub fn emit_sb_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, SB { s1: rs1, s2: rs2, im: offset })
        }
    }

    with_no_at! {
        emit_sh,
        /// Emit store halfword (SH)
        #[inline(always)]
        pub fn emit_sh_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, SH { s1: rs1, s2: rs2, im: offset })
        }
    }

    with_no_at! {
        emit_sw,
        /// Emit store word (SW)
        #[inline(always)]
        pub fn emit_sw_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, SW { s1: rs1, s2: rs2, im: offset })
        }
    }

    with_no_at! {
        emit_sd,
        /// Emit store doubleword (SD) - RV64 only
        #[inline(always)]
        pub fn emit_sd_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(
                section,
                SD { s1: rs1, s2: rs2, im: offset }
            )
        }
    }

    // ----- ARITHMETIC OPERATIONS -----

    with_no_at! {
        emit_add,
        /// Emit ADD instruction
        #[inline(always)]
        pub fn emit_add_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, ADD { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_sub,
        /// Emit SUB instruction
        #[inline(always)]
        pub fn emit_sub_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, SUB { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_addi,
        /// Emit ADDI instruction
        #[inline(always)]
        pub fn emit_addi_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, ADDI { d: rd, s: rs1, im })
        }
    }

    with_no_at! {
        emit_li32,
        /// Load 32-bit immediate value into register (pseudo-instruction)
        #[inline(always)]
        pub fn emit_li32_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            im: i32
        ) -> u64 {
            let bytes = pseudo::encode_li32_little(rd, im);
            self.emit_bytes_at(section, bytes)
        }
    }

    with_no_at! {
        emit_li64,
        /// Load 64-bit immediate value into register (pseudo-instruction)
        #[inline(always)]
        pub fn emit_li64_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            im: i64
        ) -> u64 {
            let bytes = pseudo::encode_li64_little(rd, im);
            self.emit_bytes_at(section, bytes)
        }
    }

    with_no_at! {
        emit_li,
        /// Load immediate value into register (pseudo-instruction)
        #[inline(always)]
        pub fn emit_li_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            imm: i64
        ) -> u64 {
            match self.arch {
                Arch::Riscv32 => self.emit_li32_at(section, rd, imm as i32),
                Arch::Riscv64 => self.emit_li64_at(section, rd, imm),
            }
        }
    }

    with_no_at! {
        emit_mv,
        /// Move register to register (pseudo-instruction: ADDI rd, rs, 0)
        #[inline(always)]
        pub fn emit_mv_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs: Reg
        ) -> u64 {
            self.emit_addi_at(section, rd, rs, 0)
        }
    }

    // ----- LOGICAL OPERATIONS -----

    with_no_at! {
        emit_and,
        #[inline(always)]
        pub fn emit_and_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, AND { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_or,
        #[inline(always)]
        pub fn emit_or_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, OR { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_xor,
        #[inline(always)]
        pub fn emit_xor_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, XOR { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_andi,
        #[inline(always)]
        pub fn emit_andi_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, ANDI { d: rd, s: rs1, im })
        }
    }

    with_no_at! {
        emit_ori,
        #[inline(always)]
        pub fn emit_ori_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, ORI { d: rd, s: rs1, im })
        }
    }

    with_no_at! {
        emit_xori,
        #[inline(always)]
        pub fn emit_xori_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, XORI { d: rd, s: rs1, im })
        }
    }

    // ----- SHIFT OPERATIONS -----

    with_no_at! {
        emit_sll,
        #[inline(always)]
        pub fn emit_sll_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, SLL { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_srl,
        #[inline(always)]
        pub fn emit_srl_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, SRL { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_sra,
        #[inline(always)]
        pub fn emit_sra_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, SRA { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_slli,
        #[inline(always)]
        pub fn emit_slli_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            shamt: u8
        ) -> u64 {
            self.emit_bytes_at(section, SLLI { d: rd, s: rs1, shamt })
        }
    }

    with_no_at! {
        emit_srli,
        #[inline(always)]
        pub fn emit_srli_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            shamt: u8
        ) -> u64 {
            self.emit_bytes_at(section, SRLI { d: rd, s: rs1, shamt })
        }
    }

    with_no_at! {
        emit_srai,
        #[inline(always)]
        pub fn emit_srai_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            shamt: u8
        ) -> u64 {
            self.emit_bytes_at(section, SRAI { d: rd, s: rs1, shamt })
        }
    }

    // ----- COMPARISON OPERATIONS -----

    with_no_at! {
        emit_slt,
        #[inline(always)]
        pub fn emit_slt_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, SLT { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_sltu,
        #[inline(always)]
        pub fn emit_sltu_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            rs2: Reg
        ) -> u64 {
            self.emit_bytes_at(section, SLTU { d: rd, s1: rs1, s2: rs2 })
        }
    }

    with_no_at! {
        emit_slti,
        #[inline(always)]
        pub fn emit_slti_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            im: i16
        ) -> u64 {
            self.emit_bytes_at(section, SLTI { d: rd, s: rs1, im })
        }
    }

    // ----- BRANCHING OPERATIONS -----

    with_no_at! {
        emit_beq,
        #[inline(always)]
        pub fn emit_beq_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, BEQ { s1: rs1, s2: rs2, im: 0 })
        }
    }

    with_no_at! {
        emit_bne,
        #[inline(always)]
        pub fn emit_bne_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, BNE { s1: rs1, s2: rs2, im: 0 })
        }
    }

    with_no_at! {
        emit_blt,
        #[inline(always)]
        pub fn emit_blt_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, BLT { s1: rs1, s2: rs2, im: 0 })
        }
    }

    with_no_at! {
        emit_bge,
        #[inline(always)]
        pub fn emit_bge_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, BGE { s1: rs1, s2: rs2, im: 0 })
        }
    }

    with_no_at! {
        emit_bltu,
        #[inline(always)]
        pub fn emit_bltu_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, BLTU { s1: rs1, s2: rs2, im: 0 })
        }
    }

    with_no_at! {
        emit_bgeu,
        #[inline(always)]
        pub fn emit_bgeu_at(
            &mut self,
            section: SectionId,
            rs1: Reg,
            rs2: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, BGEU { s1: rs1, s2: rs2, im: 0 })
        }
    }

    // ----- JUMP OPERATIONS -----

    with_no_at! {
        emit_jal,
        #[inline(always)]
        pub fn emit_jal_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            label: LabelId
        ) -> u64 {
            self.emit_branch_to_at(section, label, JAL { d: rd, im: 0 })
        }
    }

    with_no_at! {
        emit_jalr,
        #[inline(always)]
        pub fn emit_jalr_at(
            &mut self,
            section: SectionId,
            rd: Reg,
            rs1: Reg,
            offset: i16
        ) -> u64 {
            self.emit_bytes_at(section, JALR { d: rd, s: rs1, im: offset })
        }
    }

    // ----- PSEUDO OPS EMISSION -----

    // --- JUMP OPERATIONS ---

    with_no_at! {
        emit_jmp,
        /// Jump to label (pseudo-instruction: JAL x0, label)
        #[inline(always)]
        pub fn emit_jmp_at(
            &mut self,
            section: SectionId,
            lbl_id: LabelId
        ) -> u64 {
            self.emit_jal_at(section, ZERO, lbl_id)
        }
    }

    with_no_at! {
        emit_ret,
        /// Return from function (pseudo-instruction: JALR x0, ra, 0)
        #[inline(always)]
        pub fn emit_ret_at(
            &mut self,
            section: SectionId
        ) -> u64 {
            self.emit_jalr_at(section, ZERO, RA, 0)
        }
    }

    with_no_at! {
        emit_nop,
        /// No operation (ADDI x0, x0, 0)
        #[inline(always)]
        pub fn emit_nop_at(
            &mut self,
            section: SectionId
        ) -> u64 {
            self.emit_addi_at(section, ZERO, ZERO, 0)
        }
    }

    with_no_at! {
        emit_push,
        /// Push register onto stack
        #[inline(always)]
        pub fn emit_push_at(
            &mut self,
            section: SectionId,
            reg: Reg
        ) -> u64 {
            let ptr_size = self.address_bytes() as i16;
            self.emit_addi_at(section, SP, SP, -ptr_size);
            self.emit_sd_at(section, SP, reg, 0)
        }
    }

    with_no_at! {
        emit_pop,
        /// Pop register from stack
        #[inline(always)]
        pub fn emit_pop_at(
            &mut self,
            section: SectionId,
            reg: Reg
        ) -> u64 {
            let ptr_size = self.address_bytes() as i16;
            self.emit_ld_at(section, reg, SP, 0);
            self.emit_addi_at(section, SP, SP, ptr_size)
        }
    }
}
