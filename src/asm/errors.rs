use crate::asm::Assembler;
#[cfg(feature = "std")]
use crate::util::diag::{
    self,
    DiagnosticRenderer,
    UnplacedLabelDiagnostic
};

use core::{fmt, mem, panic};

use rustc_hash::FxHashMap;

#[derive(Debug)]
pub(crate) struct UnplacedLabelInfo {
    pub(crate) caller_loc: &'static panic::Location<'static>
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

impl FinishError {
    pub fn from_asm(mut asm: Assembler) -> FinishError {
        #[cfg(feature = "std")]
        use std::{fs, sync::Arc};

        #[cfg(feature = "std")]
        #[allow(clippy::default_constructed_unit_structs)]
        let renderer = DiagnosticRenderer::default();

        #[cfg(feature = "std")]
        let mut file_cache = FxHashMap::<_, Arc<str>>::default();

        let unplaced_labels = mem::take(&mut asm.unplaced_labels);

        let reports = unplaced_labels.into_iter().map(|(lbl_id, info)| {
            let label = asm.get_label(lbl_id);
            let name_bytes = asm.get_symbol_name(label.sym);
            let label_name = str::from_utf8(name_bytes)
                .unwrap_or("<invalid UTF-8>")
                .to_owned();

            let file_path = info.caller_loc.file();

            #[cfg(feature = "no_std")] {
                format!{
                    "error: unplaced label '{label_name}'\n --> {f}:{l}:{c}",
                    f = file_path,
                    l = info.caller_loc.line(),
                    c = info.caller_loc.column()
                }
            }

            #[cfg(feature = "std")] {
                let content = file_cache.entry(file_path).or_insert_with(|| {
                    fs::read_to_string(file_path).unwrap_or_default().into()
                });

                let (named_src, span) = diag::text_into_named_source_and_span(
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
            }
        }).collect::<Vec<_>>();

        FinishError {
            // join multiple diagnostics with a blank line between them
            rendered: reports.join("\n\n")
        }
    }

}
