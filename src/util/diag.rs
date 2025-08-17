//! Diagnostic helpers

use crate::util::misc;
#[cfg(not(feature = "fancy-diagnostics"))]
use crate::asm::errors::UnplacedLabelDiagnostic;

use std::sync::Arc;
use std::string::String;

use memchr::Memchr;

#[cfg(feature = "fancy-diagnostics")]
use miette::{
    Diagnostic,
    SourceSpan,
    SourceCode,
    NamedSource,
    MietteError,
    SpanContents,
    GraphicalReportHandler,
};

/// A span representing a location in the source code (offset and length).
#[derive(Copy, Debug, Clone)]
pub struct BrikSourceSpan {
    pub offset: usize,
    pub length: usize,
}

impl BrikSourceSpan {
    #[inline(always)]
    pub const fn new(offset: usize, length: usize) -> Self {
        Self { offset, length }
    }
}

#[cfg(feature = "fancy-diagnostics")]
impl From<BrikSourceSpan> for SourceSpan {
    #[inline(always)]
    fn from(span: BrikSourceSpan) -> Self {
        SourceSpan::from(span.offset..span.offset + span.length)
    }
}

/// A named source file with its content.
#[derive(Debug, Clone)]
pub struct BrikNamedSource {
    pub name: Arc<str>,
    pub source: Arc<str>,
}

impl BrikNamedSource {
    #[inline(always)]
    pub fn new(name: impl Into<Arc<str>>, content: impl Into<Arc<str>>) -> Self {
        Self { name: name.into(), source: content.into() }
    }

    #[inline(always)]
    pub fn file_name(&self) -> &str { &self.name }

    #[inline(always)]
    pub fn inner(&self) -> &str { &self.source }
}

#[cfg(feature = "fancy-diagnostics")]
impl From<BrikNamedSource> for NamedSource {
    #[inline(always)]
    fn from(src: BrikNamedSource) -> Self {
        NamedSource::new(src.name, src.source)
    }
}

#[cfg(feature = "fancy-diagnostics")]
impl SourceCode for BrikNamedSource {
    #[inline(always)]
    fn read_span<'a>(
        &'a self,
        span: &SourceSpan,
        context_lines_before: usize,
        context_lines_after: usize,
    ) -> Result<Box<dyn SpanContents<'a> + 'a>, MietteError> {
        self.source.read_span(span, context_lines_before, context_lines_after)
    }
}

#[derive(Default)]
#[cfg(not(feature = "fancy-diagnostics"))]
pub struct DiagnosticRenderer {}

#[cfg(feature = "fancy-diagnostics")]
pub struct DiagnosticRenderer {
    handler: GraphicalReportHandler,
}

#[cfg(feature = "fancy-diagnostics")]
impl Default for DiagnosticRenderer {
    #[inline(always)]
    fn default() -> Self {
        Self { handler: GraphicalReportHandler::new() }
    }
}

impl DiagnosticRenderer {
    #[inline]
    #[cfg(feature = "fancy-diagnostics")]
    pub fn render_to_string(&self, diag: &impl Diagnostic) -> String {
        const RENDERED_PREALLOCATION_SIZE: usize = 512;

        let mut rendered = String::with_capacity(RENDERED_PREALLOCATION_SIZE);
        self.handler
            .render_report(&mut rendered, diag)
            .expect("render_report should not fail");

        rendered
    }

    // TODO(#8): Generalize `diag` param type in not(fancy-diagnostics)
    // in DiagnosticRenderer::render_to_string

    #[inline]
    #[cfg(not(feature = "fancy-diagnostics"))]
    pub fn render_to_string(&self, diag: &UnplacedLabelDiagnostic) -> String {
        use std::string::ToString;

        let src_name = diag.src.file_name();
        let src_content = diag.src.inner();
        let src_content_bytes = src_content.as_bytes();
        let span_start = diag.span.offset;
        let span_len = diag.span.length;

        let line_start = memchr::memrchr(b'\n', &src_content_bytes[..span_start])
            .map(|i| i + 1)
            .unwrap_or(0);

        let line_end = memchr::memchr(b'\n', &src_content_bytes[span_start..])
            .map(|i| span_start + i)
            .unwrap_or(src_content.len());

        let line = &src_content[line_start..line_end];
        let line_number = bytecount::count(
            &src_content.as_bytes()[..line_start],
            b'\n'
        ) + 1;

        let column = span_start - line_start + 1;

        // -> error
        let caret = " ".repeat(column - 1) + &"^".repeat(span_len);

        let line_number_str = line_number.to_string();
        let line_number_pad = " ".repeat(line_number_str.len());

        std::format!{
            "error: unplaced label '{name}'\n  --> {src_name}:{lnum}:{c}\n{lpad} |\n{lstr} | {line}\n{lpad} | {caret}\n",
            name = diag.name,
            lnum = line_number,
            c = column,
            lpad = line_number_pad,
            lstr = line_number_str,
        }
    }
}

#[inline(always)]
const fn byte_offset_from_line_offsets(
    line_start : usize,
    line_end   : usize,
    target_col : usize
) -> usize {
    let line_len = line_end - line_start;
    let col0 = misc::b0(target_col, line_len);
    line_start + col0
}

#[inline]
pub fn text_into_named_source_and_span(
    text_     : impl AsRef<str> + Into<Arc<str>> + Clone,
    file_path : impl AsRef<str>,

    line          : usize,
    column        : usize,
    highlight_len : usize
) -> (BrikNamedSource, BrikSourceSpan) {
    let text = text_.as_ref();
    let file_path = file_path.as_ref();

    if !text.is_empty() {
        const CONTENT_SIZE_THRESHOLD: usize = 10 * 1024;

        let line = misc::b0(line, line);

        let byte_offset = if text.len() < CONTENT_SIZE_THRESHOLD {
            calculate_byte_offset_small(text, line, column)
        } else {
            calculate_byte_offset_large(text, line, column)
        };

        (
            BrikNamedSource::new(file_path, text_.clone()),
            BrikSourceSpan::new(byte_offset, highlight_len),
        )
    } else {
        (
            BrikNamedSource::new(file_path, ""),
            BrikSourceSpan::new(0, 0)
        )
    }
}

pub fn calculate_byte_offset_small(text: &str, target_line: usize, target_col: usize) -> usize {
    if target_line == 0 {
        return misc::b0(target_col, text.len())
    }

    let mut curr_line = 0;
    let mut last_newline_pos = 0;

    let mut newline_iter = Memchr::new(b'\n', text.as_bytes());
    while let Some(pos) = newline_iter.next() {
        if curr_line + 1 == target_line {
            let line_start = pos + 1;
            let line_end = newline_iter.next().unwrap_or(text.len());
            return byte_offset_from_line_offsets(
                line_start,
                line_end,
                target_col
            )
        }

        curr_line += 1;
        last_newline_pos = pos;
    }

    // target line is beyond the file -> use end of file
    let final_offset = misc::b0(
        target_col,
        text.len() - last_newline_pos
    );

    last_newline_pos + final_offset
}

pub fn calculate_byte_offset_large(text: &str, target_line: usize, target_col: usize) -> usize {
    const FINAL_MEMCHR_THRESHOLD : usize = 1024;
    const BYTECOUNT_CHUNK_SIZE   : usize = 1024 * 8;

    if target_line == 0 {
        return misc::b0(target_col, text.len());
    }

    let text_bytes = text.as_bytes();
    let mut lines_seen = 0;
    let mut search_start = 0;

    // pass search_start explicitly to avoid borrow conflict
    let find_line_end_and_calculate_byte_offset = |last_nl_pos: usize, search_start: usize| {
        let line_start = search_start + last_nl_pos + 1;
        let line_end = memchr::memchr(b'\n', &text_bytes[line_start..])
            .map(|p| line_start + p)
            .unwrap_or(text.len());

        byte_offset_from_line_offsets(line_start, line_end, target_col)
    };

    while lines_seen < target_line && search_start < text_bytes.len() {
        let remaining = &text_bytes[search_start..];

        if remaining.len() < FINAL_MEMCHR_THRESHOLD {
            let Some(pos) = memchr::memchr(b'\n', remaining) else {
                break
            };

            lines_seen += 1;

            if lines_seen == target_line {
                return find_line_end_and_calculate_byte_offset(
                    pos,
                    search_start
                )
            }

            search_start += pos + 1;
        } else {
            let chunk_end = (search_start + BYTECOUNT_CHUNK_SIZE).min(text_bytes.len());
            let chunk = &text_bytes[search_start..chunk_end];
            let newlines_in_chunk = bytecount::count(chunk, b'\n');

            if lines_seen + newlines_in_chunk >= target_line {
                let mut local_search = 0;
                for pos in Memchr::new(b'\n', &chunk[local_search..]) {
                    lines_seen += 1;

                    if lines_seen == target_line {
                        return find_line_end_and_calculate_byte_offset(
                            local_search + pos,
                            search_start
                        )
                    }

                    local_search += pos + 1;
                }

                break
            } else {
                lines_seen += newlines_in_chunk;
                search_start = chunk_end;
            }
        }
    }

    let final_offset = misc::b0(target_col, text.len() - search_start);
    search_start + final_offset
}
