use crate::ast::Span;

pub fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, b) in source.bytes().enumerate() {
        if b == b'\n' {
            starts.push(i + 1);
        }
    }
    starts
}

pub fn span_to_byte_range(source: &str, span: &Span) -> Option<(usize, usize)> {
    span_to_byte_range_with_starts(&line_starts(source), span)
}

/// Same as `span_to_byte_range`, but takes an already-computed `line_starts`
/// table - for callers that convert many spans against the same source and
/// would otherwise re-scan the whole source (an O(source_len) pass) on every
/// single call.
pub fn span_to_byte_range_with_starts(starts: &[usize], span: &Span) -> Option<(usize, usize)> {
    if let Span::Known(_, lo, hi) = span {
        let lo_byte = starts.get(lo.0).map(|s| s + lo.1)?;
        let hi_byte = starts.get(hi.0).map(|s| s + hi.1)?;
        Some((lo_byte, hi_byte))
    } else {
        None
    }
}

pub fn source_text<'a>(source: &'a str, span: &Span) -> Option<&'a str> {
    let (lo, hi) = span_to_byte_range(source, span)?;
    source.get(lo..hi)
}

/// Same as `source_text`, but takes an already-computed `line_starts` table -
/// see `span_to_byte_range_with_starts`.
pub fn source_text_with_starts<'a>(
    source: &'a str,
    starts: &[usize],
    span: &Span,
) -> Option<&'a str> {
    let (lo, hi) = span_to_byte_range_with_starts(starts, span)?;
    source.get(lo..hi)
}
