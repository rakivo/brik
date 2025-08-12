//! Object file builder

use crate::util::{diag, rv64};
use crate::asm_riscv::{I, Reg};
use crate::util::into_bytes::IntoBytes;
use crate::reloc::{Reloc, PcrelPart, RelocKind};
use crate::util::attr_builder::RiscvAttrsBuilder;
use crate::util::diag::{
    DiagnosticRenderer,
    UnplacedLabelDiagnostic
};
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

use std::sync::Arc;
use std::ops::{Deref, DerefMut};
use std::{fs, mem, str, fmt, panic};

use rustc_hash::FxHashMap;

#[derive(Eq, Ord, Hash, Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct LabelId(usize);

#[derive(Copy, Clone, Debug)]
pub struct Label {
    sym: SymbolId,
}

#[derive(Debug)]
pub struct UnplacedLabelInfo {
    caller_loc: &'static panic::Location<'static>
}

/// The FinishError stores the pre-rendered, pretty error text.
pub struct FinishError {
    /// Rendered miette diagnostic(s)
    pub rendered: String,
}

debug_from_display!(FinishError, newline);

impl fmt::Display for FinishError {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { rendered } = self;
        write!(f, "{rendered}")
    }
}

/// Object file builder
#[derive(Debug)]
pub struct Assembler<'a> {
    obj: Object<'a>,
    relocs: Vec<(SectionId, Reloc)>,
    curr_section: Option<SectionId>,

    pcrel_counter: u32,
    lbl_id_counter: LabelId,

    labels          : FxHashMap<LabelId, Label>,
    unplaced_labels : FxHashMap<LabelId, UnplacedLabelInfo>,
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

    /// Create a new `Assembler` instance.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brik::{asm, object};
    /// let mut asm = asm::Assembler::new(
    ///     object::BinaryFormat::Elf,
    ///     object::Architecture::Riscv64,
    ///     object::Endianness::Little,
    ///     "rv64gc",
    /// );
    /// ```
    pub fn new(
        format: BinaryFormat,
        arch: Architecture,
        endian: Endianness,
        isa: &str
    ) -> Self {
        let mut asm = Self {
            pcrel_counter: 0,
            lbl_id_counter: LabelId(0),
            curr_section: None,
            labels: FxHashMap::default(),
            unplaced_labels: FxHashMap::default(),
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

    /// Finish object emission
    #[inline]
    pub fn finish(mut self) -> Result<Object<'a>, FinishError> {
        if self.unplaced_labels.is_empty() {
            self.resolve_local_relocs();
            self.resolve_final_relocs();
            return Ok(self.obj)
        }

        Err(self.into_finish_error())
    }

    #[inline(always)]
    pub const fn position_at_end(&mut self, section: SectionId) {
        self.curr_section = Some(section)
    }

    #[inline(always)]
    pub const fn set_object_flags(&mut self, flags: FileFlags) {
        self.obj.flags = flags
    }

    #[must_use]
    #[inline(always)]
    pub fn curr_offset(&self) -> u64 {
        let sid = self.expect_curr_section();
        self.section_size(sid)
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
    pub const fn expect_curr_section(&self) -> SectionId {
        self.curr_section().expect("no current section set")
    }

    #[must_use]
    #[inline(always)]
    pub fn section_size(&self, section_id: SectionId) -> u64 {
        self.obj.section(section_id).data().len() as _
    }

    with_at_end!{
        /// Add a text section
        #[inline(always)]
        pub fn add_text_section(&mut self, name: &[u8]) -> SectionId {
            self.add_section(
                StandardSegment::Text,
                name,
                SectionKind::Text,
            )
        }
    }

    with_at_end!{
        /// Add a data section
        #[inline]
        pub fn add_data_section(&mut self, name: &[u8]) -> SectionId {
            self.add_section(
                StandardSegment::Data,
                name,
                SectionKind::Data
            )
        }
    }

    with_at_end!{
        /// Add a read-only data section
        #[inline]
        pub fn add_rodata_section(&mut self, name: &[u8]) -> SectionId {
            self.add_section(
                StandardSegment::Data,
                name,
                SectionKind::ReadOnlyData
            )
        }
    }

    with_at_end!{
        /// Add a BSS section
        #[inline]
        pub fn add_bss_section(&mut self, name: &[u8]) -> SectionId {
            self.add_section(
                StandardSegment::Data,
                name,
                SectionKind::UninitializedData
            )
        }
    }

    with_at_end!{
        #[inline]
        pub fn add_section(
            &mut self,
            segment: StandardSegment,
            name: &[u8],
            kind: SectionKind,
        ) -> SectionId {
            self.obj.add_section(
                self.segment_name(segment).to_vec(),
                name.to_vec(),
                kind,
            )
        }
    }

    // -----

    fn into_finish_error(mut self) -> FinishError {
        let renderer = DiagnosticRenderer::new();

        let mut file_cache = FxHashMap::<_, Arc<str>>::default();

        let unplaced_labels = mem::take(&mut self.unplaced_labels);

        let reports = unplaced_labels.into_iter().map(|(lbl_id, info)| {
            let label = self.get_label(lbl_id);
            let name_bytes = self.get_symbol_name(label.sym);
            let label_name = str::from_utf8(name_bytes)
                .unwrap_or("<invalid UTF-8>")
                .to_owned();

            let file_path = info.caller_loc.file();

            let content = file_cache.entry(file_path).or_insert_with(|| {
                fs::read_to_string(&file_path).unwrap_or_default().into()
            });

            let (named_src, span) = diag::text_into_named_source_and_source_span(
                Arc::clone(content),
                file_path,
                info.caller_loc.line() as _,
                info.caller_loc.column() as _,
                label_name.len().max(1)
            );

            let diag = UnplacedLabelDiagnostic {
                span,
                src: named_src,
                name: label_name
            };

            renderer.render_to_string(&diag)
        }).collect::<Vec<_>>();

        FinishError {
            // join multiple diagnostics with a blank line between them
            rendered: reports.join("\n\n")
        }
    }

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
    fn add_label_(&mut self, name: &[u8], offset: u64) -> Label {
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
    pub fn add_label_here(&mut self, name: &[u8]) -> LabelId {
        let curr_offset = self.curr_offset();
        let l = self.add_label_(name, curr_offset);
        let id = self.next_brik_lbl_id();
        self.labels.insert(id, l);
        id
    }

    #[inline]
    #[track_caller]
    pub fn declare_label(&mut self, name: &[u8]) -> LabelId {
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

    pub fn resolve_local_relocs(&mut self) {
        fn apply_reloc(data: &mut [u8], rtype: RelocKind, delta: i64) {
            match rtype {
                RelocKind::Branch => {
                    if !(-4096..=4094).contains(&delta) || delta % 2 != 0 {
                        panic!("Branch offset out of range: {delta}");
                    }

                    let imm13 = delta as i32;
                    let mut inst = u32::from_le_bytes(
                        data.try_into().expect("invalid instruction length")
                    );

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
                    let mut inst = u32::from_le_bytes(
                        data.try_into().expect("invalid instruction length")
                    );

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

                    inst.copy_into(&mut data[0..4]);
                    jalr_inst.copy_into(&mut data[4..8]);
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
    pub fn emit_branch_to(&mut self, lbl_id: LabelId, i: asm_riscv::I) {
        let section_id = self.expect_curr_section();
        let offset = self.emit_bytes(i);

        let rtype = match i {
            I::JAL { .. } => RelocKind::Jal,
            I::BEQ { .. }  | I::BNE { .. } |
            I::BLT { .. }  | I::BGE { .. } |
            I::BLTU { .. } | I::BGEU { .. } => RelocKind::Branch,
            _ => unimplemented!("unsupported branch instruction type"),
        };

        self.relocs.push((
            section_id,
            Reloc {
                offset,
                symbol: self.get_label(lbl_id).sym,
                rtype,
                addend: 0,
            }
        ));
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

    #[inline(always)]
    pub fn try_remove_from_unplaced(&mut self, lbl_id: LabelId) {
        _ = self.unplaced_labels.remove(&lbl_id)
    }

    #[inline]
    pub fn place_label_at(&mut self, lbl_id: LabelId, offset: u64) {
        let label = self.get_label(lbl_id);
        let sym = &mut self.obj.symbol_mut(label.sym);
        sym.value = offset;
        self.try_remove_from_unplaced(lbl_id);
    }

    #[inline]
    pub fn place_label_here(&mut self, lbl_id: LabelId) {
        let section_id = self.expect_curr_section();
        let offset = self.section_size(section_id) as u64;
        self.place_label_at(lbl_id, offset);
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

    #[inline]
    pub fn emit_bytes_with_reloc_at(
        &mut self,
        data: impl IntoBytes<'a>,
        section: SectionId,
        (symbol, rtype): (SymbolId, RelocKind),
    ) -> u64 {
        let offset = self.obj.append_section_data(
            section,
            &data.into_bytes(),
            1 // align
        );

        self.add_reloc(section, Reloc {
            offset,
            symbol,
            rtype,
            addend: 0
        });

        offset
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

    // ----- OPS EMISSION -----

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

    #[inline(always)]
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

    // ----- LOAD/STORE OPERATIONS -----

    /// Emit load byte (LB)
    #[inline(always)]
    pub fn emit_lb(&mut self, rd: Reg, rs1: Reg, offset: i16) {
        self.emit_bytes(I::LB { d: rd, s: rs1, im: offset });
    }

    /// Emit load halfword (LH)
    #[inline(always)]
    pub fn emit_lh(&mut self, rd: Reg, rs1: Reg, offset: i16) {
        self.emit_bytes(I::LH { d: rd, s: rs1, im: offset });
    }

    /// Emit load word (LW)
    #[inline(always)]
    pub fn emit_lw(&mut self, rd: Reg, rs1: Reg, offset: i16) {
        self.emit_bytes(I::LW { d: rd, s: rs1, im: offset });
    }

    /// Emit load doubleword (LD) - RV64 only
    #[inline(always)]
    pub fn emit_ld(&mut self, rd: Reg, rs1: Reg, offset: i16) {
        self.emit_bytes(rv64::encode_ld(rd, rs1, offset));
    }

    /// Emit store byte (SB)
    #[inline(always)]
    pub fn emit_sb(&mut self, rs1: Reg, rs2: Reg, offset: i16) {
        self.emit_bytes(I::SB { s1: rs1, s2: rs2, im: offset });
    }

    /// Emit store halfword (SH)
    #[inline(always)]
    pub fn emit_sh(&mut self, rs1: Reg, rs2: Reg, offset: i16) {
        self.emit_bytes(I::SH { s1: rs1, s2: rs2, im: offset });
    }

    /// Emit store word (SW)
    #[inline(always)]
    pub fn emit_sw(&mut self, rs1: Reg, rs2: Reg, offset: i16) {
        self.emit_bytes(I::SW { s1: rs1, s2: rs2, im: offset });
    }

    /// Emit store doubleword (SD) - RV64 only
    #[inline(always)]
    pub fn emit_sd(&mut self, rs1: Reg, rs2: Reg, offset: i16) {
        self.emit_bytes(rv64::encode_sd(rs1, rs2, offset));
    }

    // ----- ARITHMETIC OPERATIONS -----

    /// Emit ADD instruction
    #[inline(always)]
    pub fn emit_add(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::ADD { d: rd, s1: rs1, s2: rs2 });
    }

    /// Emit SUB instruction
    #[inline(always)]
    pub fn emit_sub(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::SUB { d: rd, s1: rs1, s2: rs2 });
    }

    /// Emit ADDI instruction
    #[inline(always)]
    pub fn emit_addi(&mut self, rd: Reg, rs1: Reg, im: i16) {
        self.emit_bytes(I::ADDI { d: rd, s: rs1, im });
    }

    /// Load immediate value into register (pseudo-instruction)
    #[inline(always)]
    pub fn emit_li(&mut self, rd: Reg, imm: i64) {
        let bytes = rv64::encode_li_rv64_little(rd, imm);
        self.emit_bytes(bytes);
    }

    /// Move register to register (pseudo-instruction: ADDI rd, rs, 0)
    #[inline(always)]
    pub fn emit_mv(&mut self, rd: Reg, rs: Reg) {
        self.emit_addi(rd, rs, 0);
    }

    // ----- LOGICAL OPERATIONS -----

    #[inline(always)]
    pub fn emit_and(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::AND { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_or(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::OR { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_xor(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::XOR { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_andi(&mut self, rd: Reg, rs1: Reg, im: i16) {
        self.emit_bytes(I::ANDI { d: rd, s: rs1, im });
    }

    #[inline(always)]
    pub fn emit_ori(&mut self, rd: Reg, rs1: Reg, im: i16) {
        self.emit_bytes(I::ORI { d: rd, s: rs1, im });
    }

    #[inline(always)]
    pub fn emit_xori(&mut self, rd: Reg, rs1: Reg, im: i16) {
        self.emit_bytes(I::XORI { d: rd, s: rs1, im });
    }

    // === SHIFT OPERATIONS ===

    #[inline(always)]
    pub fn emit_sll(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::SLL { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_srl(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::SRL { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_sra(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::SRA { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_slli(&mut self, rd: Reg, rs1: Reg, shamt: i8) {
        self.emit_bytes(I::SLLI { d: rd, s: rs1, im: shamt });
    }

    #[inline(always)]
    pub fn emit_srli(&mut self, rd: Reg, rs1: Reg, shamt: i8) {
        self.emit_bytes(I::SRLI { d: rd, s: rs1, im: shamt });
    }

    #[inline(always)]
    pub fn emit_srai(&mut self, rd: Reg, rs1: Reg, shamt: i8) {
        self.emit_bytes(I::SRAI { d: rd, s: rs1, im: shamt });
    }

    // === COMPARISON OPERATIONS ===

    #[inline(always)]
    pub fn emit_slt(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::SLT { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_sltu(&mut self, rd: Reg, rs1: Reg, rs2: Reg) {
        self.emit_bytes(I::SLTU { d: rd, s1: rs1, s2: rs2 });
    }

    #[inline(always)]
    pub fn emit_slti(&mut self, rd: Reg, rs1: Reg, im: i16) {
        self.emit_bytes(I::SLTI { d: rd, s: rs1, im });
    }

    // === JUMP OPERATIONS ===

    /// Jump and link to label
    #[inline(always)]
    pub fn emit_jal(&mut self, rd: Reg, label: LabelId) {
        self.emit_branch_to(label, I::JAL { d: rd, im: 0 });
    }

    /// Jump and link register
    #[inline(always)]
    pub fn emit_jalr(&mut self, rd: Reg, rs1: Reg, offset: i16) {
        self.emit_bytes(I::JALR { d: rd, s: rs1, im: offset });
    }

    // ----- PSEUDO OPS EMISSION -----

    // --- JUMP OPERATIONS ---

    /// Jump to label (pseudo-instruction: JAL x0, label)
    #[inline(always)]
    pub fn emit_j(&mut self, lbl_id: LabelId) {
        self.emit_jal(Reg::ZERO, lbl_id);
    }

    /// Return from function (pseudo-instruction: JALR x0, ra, 0)
    #[inline(always)]
    pub fn emit_ret(&mut self) {
        self.emit_jalr(Reg::ZERO, Reg::RA, 0);
    }

    /// No operation (ADDI x0, x0, 0)
    #[inline(always)]
    pub fn emit_nop(&mut self) {
        self.emit_addi(Reg::ZERO, Reg::ZERO, 0);
    }

    /// Push register onto stack
    #[inline(always)]
    pub fn emit_push(&mut self, reg: Reg) {
        self.emit_addi(Reg::SP, Reg::SP, -8);
        self.emit_sd(Reg::SP, reg, 0);
    }

    /// Pop register from stack
    #[inline(always)]
    pub fn emit_pop(&mut self, reg: Reg) {
        self.emit_ld(reg, Reg::SP, 0);
        self.emit_addi(Reg::SP, Reg::SP, 8);
    }
}

