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

/// Maps between the byte columns hemlis uses internally (`ast::Pos.1` is a byte
/// offset within its line - see `span_to_byte_range_with_starts`) and the
/// UTF-16 code-unit columns LSP means by `Position.character` when the
/// negotiated position encoding is `utf-16`.
///
/// Built once per file, whenever that file's source is stored.
#[derive(Debug, Clone)]
pub struct LineIndex {
    /// Byte offset of the start of each line.
    starts: Vec<usize>,
    /// The file's source. Kept here so a column can be converted from an
    /// `Fi` alone, without threading the text through every caller.
    src: Box<str>,
    /// Whole-file fast path: with no multi-byte characters anywhere, byte
    /// columns and UTF-16 columns coincide and both conversions are identity.
    all_ascii: bool,
}

impl LineIndex {
    pub fn new(src: &str) -> Self {
        LineIndex {
            starts: line_starts(src),
            src: src.into(),
            all_ascii: src.is_ascii(),
        }
    }

    /// The text of `line`, excluding its trailing newline.
    fn line(&self, line: usize) -> Option<&str> {
        let start = *self.starts.get(line)?;
        let end = self
            .starts
            .get(line + 1)
            .map_or(self.src.len(), |next| next.saturating_sub(1));
        self.src.get(start..end)
    }

    /// Byte column -> UTF-16 code-unit column.
    ///
    /// Out-of-range lines and columns pass through unchanged, matching how the
    /// rest of the server treats positions it cannot resolve.
    pub fn utf16_col(&self, line: usize, byte_col: usize) -> usize {
        if self.all_ascii {
            return byte_col;
        }
        let Some(text) = self.line(line) else {
            return byte_col;
        };
        if text.is_ascii() {
            return byte_col;
        }
        let mut units = 0;
        for (byte_idx, c) in text.char_indices() {
            if byte_idx >= byte_col {
                return units;
            }
            units += c.len_utf16();
        }
        units + byte_col.saturating_sub(text.len())
    }

    /// UTF-16 code-unit column -> byte column.
    pub fn byte_col(&self, line: usize, utf16_col: usize) -> usize {
        if self.all_ascii {
            return utf16_col;
        }
        let Some(text) = self.line(line) else {
            return utf16_col;
        };
        if text.is_ascii() {
            return utf16_col;
        }
        let mut units = 0;
        for (byte_idx, c) in text.char_indices() {
            if units >= utf16_col {
                return byte_idx;
            }
            units += c.len_utf16();
        }
        text.len() + utf16_col.saturating_sub(units)
    }
}

#[cfg(test)]
mod line_index_tests {
    use super::LineIndex;

    #[test]
    fn ascii_is_identity() {
        let ix = LineIndex::new("module A where\nfoo = 1\n");
        for col in 0..14 {
            assert_eq!(ix.utf16_col(0, col), col);
            assert_eq!(ix.byte_col(0, col), col);
        }
    }

    #[test]
    fn two_byte_chars_count_as_one_utf16_unit() {
        // "-- Ã¥Ã¤Ã¶ x": each of Ã¥/Ã¤/Ã¶ is 2 bytes, 1 UTF-16 unit.
        let src = "-- \u{e5}\u{e4}\u{f6} x\n";
        let ix = LineIndex::new(src);
        // byte 3 = start of Ã¥ = UTF-16 unit 3
        assert_eq!(ix.utf16_col(0, 3), 3);
        // after the three 2-byte chars: byte 9, UTF-16 unit 6
        assert_eq!(ix.utf16_col(0, 9), 6);
        assert_eq!(ix.byte_col(0, 6), 9);
        // round-trips at every UTF-16 boundary
        for units in 0..=8 {
            assert_eq!(ix.utf16_col(0, ix.byte_col(0, units)), units);
        }
    }

    #[test]
    fn astral_chars_are_two_utf16_units() {
        // An emoji is 4 bytes and 2 UTF-16 units (a surrogate pair).
        let ix = LineIndex::new("-- \u{1f600} x\n");
        assert_eq!(ix.utf16_col(0, 3), 3);
        assert_eq!(ix.utf16_col(0, 7), 5);
        assert_eq!(ix.byte_col(0, 5), 7);
    }

    #[test]
    fn later_lines_use_their_own_offsets() {
        let ix = LineIndex::new("\u{e5} = 1\nfoo \u{f6} = 2\n");
        assert_eq!(ix.utf16_col(1, 4), 4);
        assert_eq!(ix.utf16_col(1, 6), 5);
        assert_eq!(ix.byte_col(1, 5), 6);
    }
}
