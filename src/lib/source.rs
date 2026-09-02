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
    if let Span::Known(_, lo, hi) = span {
        let starts = line_starts(source);
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
