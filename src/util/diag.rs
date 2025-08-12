use crate::util::misc;

use std::sync::Arc;

use thiserror::Error;
use memchr::Memchr;
use miette::{
    Diagnostic,
    SourceSpan,
    NamedSource,
    GraphicalReportHandler,
};

#[derive(Debug, Error, Diagnostic)]
#[error("unplaced label '{name}'")]
pub struct UnplacedLabelDiagnostic {
    /// Will be rendered above the snippet as the main error message
    #[diagnostic(code(brik::unplaced_label))]
    pub name: String,

    /// The span inside `src` that should be highlighted
    #[label("label never placed")]
    pub span: SourceSpan,

    /// The source file content (miette prints this)
    #[source_code]
    pub src: NamedSource
}

pub struct DiagnosticRenderer {
    handler: GraphicalReportHandler,
}

impl Default for DiagnosticRenderer {
    #[inline(always)]
    fn default() -> Self {
        Self { handler: GraphicalReportHandler::new() }
    }
}

impl DiagnosticRenderer {
    const RENDERED_PREALLOCATION_SIZE: usize = 512;

    #[inline]
    pub fn render_to_string(&self, diag: &impl Diagnostic) -> String {
        let mut rendered = String::with_capacity(
            Self::RENDERED_PREALLOCATION_SIZE
        );

        self.handler
            .render_report(&mut rendered, diag)
            .expect("render_report should not fail");

        rendered
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
pub fn text_into_named_source_and_source_span(
    text      : impl Into<Arc<str>>,
    file_path : impl AsRef<str>,

    line          : usize,
    column        : usize,
    highlight_len : usize
) -> (NamedSource, SourceSpan) {
    let text = text.into();

    if !text.is_empty() {
        const CONTENT_SIZE_THRESHOLD: usize = 10 * 1024;

        let line = misc::b0(line, line);

        let byte_offset = if text.len() < CONTENT_SIZE_THRESHOLD {
            calculate_byte_offset_small(&text, line, column)
        } else {
            calculate_byte_offset_large(&text, line, column)
        };

        (
            NamedSource::new(file_path, Arc::clone(&text)),
            SourceSpan::new(byte_offset.into(), highlight_len.into()),
        )
    } else {
        (
            NamedSource::new(file_path, ""),
            SourceSpan::new(0.into(), 0.into())
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

