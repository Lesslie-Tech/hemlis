#![allow(non_snake_case)]

use logos::Logos;

use crate::ast::{Fi, Span};
// NOTE: Might not support unicode?

fn lex_raw_string<'t>(lex: &mut logos::Lexer<'t, Token<'t>>) -> Option<&'t str> {
    while let Some(at) = lex.remainder().find("\"\"\"") {
        match lex.remainder().get(at + 3..at + 4) {
            Some("\"") => {
                lex.bump(at + 1);
            }
            _ => {
                lex.bump(at + 3);
                let s = lex.slice();
                return Some(&s[3..s.len() - 3]);
            }
        }
    }
    None
}

fn lex_block_comment<'t>(lex: &mut logos::Lexer<'t, Token<'t>>) -> Option<&'t str> {
    if let Some(at) = lex.remainder().find("-}") {
        lex.bump(at + 2);
        return Some(lex.slice());
    }
    None
}

fn lex_indent<'t>(lex: &mut logos::Lexer<'t, Token<'t>>) -> usize {
    let at = lex.slice().rfind("\n").unwrap_or(0);
    lex.span()
        .end
        .saturating_sub(lex.span().start)
        .saturating_sub(at)
        .saturating_sub(1)
}

fn lex_qual<'t>(lex: &mut logos::Lexer<'t, Token<'t>>) -> &'t str {
    while let Some(at) = lex.remainder().find(".") {
        if !lex
            .remainder()
            .get(0..(at.saturating_sub(1)))
            .map(|x| {
                x.chars().take(1).all(|x| x.is_uppercase())
                    && x.chars().skip(1).all(|x| x.is_alphanumeric())
            })
            .unwrap_or(false)
        {
            break;
        }
        lex.bump(at + 1);
    }
    lex.slice()
}

fn lex_symbol<'t>(lex: &mut logos::Lexer<'t, Token<'t>>) -> &'t str {
    if let Some(at) = lex.remainder().find(")") {
        if at != 0
            && lex
                .remainder()
                .get(0..at)
                .map(|x| {
                    x.chars().all(|x| {
                        matches!(
                            x,
                            '!' | '#'
                                | '$'
                                | '%'
                                | '&'
                                | '*'
                                | '+'
                                | '.'
                                | '-'
                                | '\\'
                                | '|'
                                | '/'
                                | '<'
                                | '='
                                | '>'
                                | '?'
                                | '@'
                                | '^'
                                | '~'
                                | ':'
                                | ';'
                                | '¤'
                        )
                    })
                })
                .unwrap_or(false)
        {
            lex.bump(at + 1);
        }
    }
    lex.slice()
}

#[derive(Logos, Debug, PartialEq, Eq, Clone, Copy)]
#[logos()]
pub enum Token<'t> {
    #[regex("\\s+", logos::skip)]
    // Conflicts with symbol too-much
    // #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,
    #[token("[")]
    LeftSquare,
    #[token("]")]
    RightSquare,

    // Conclifcts with operators
    LeftArrow,
    RightArrow,
    RightFatArrow,
    Pipe,
    Slash,
    ColonColon,
    At,
    Equals,

    #[token("`")]
    Tick,
    #[token(",")]
    Comma,

    #[token("infixr")]
    Infixr,
    #[token("infixl")]
    Infixl,
    #[token("infix")]
    Infix,
    #[token("derive")]
    Derive,
    #[token("newtype")]
    Newtype,
    #[token("foreign")]
    Foreign,
    #[token("instance")]
    Instance,

    #[token("where")]
    Where,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("case")]
    Case,
    #[token("of")]
    Of,
    #[token("let")]
    Let,
    #[token("do")]
    Do,
    #[token("ado")]
    Ado,

    // TODO: We need to parse this with a custom function, We can eat greadily if we tokenize
    // ourselves here.
    #[regex("[A-Z][[:alnum:]]*\\.", |lex| lex_qual(lex))]
    Qual(&'t str),

    // TODO: Might be too much of a wuzz when only extending the uncide with swedish
    #[regex("[_a-zåäö][[:alnum:]'åäöÅÄÖ_]*")]
    Lower(&'t str),

    #[regex("[A-ZÅÄÖ][[:alnum:]'åäöÅÄÖ_]*", priority = 20)]
    Upper(&'t str),

    #[regex(r"[!|#|$|%|&|*|+|.|\-|\||\\|/|<|=|>|?|@|^|~|:|;|¤]+")]
    Op(&'t str),

    #[token("(", |lex| lex_symbol(lex))]
    SymbolOrParen(&'t str),

    Symbol(&'t str),

    #[regex("\\?[_a-z][[:alnum:]]*")]
    Hole(&'t str),

    #[regex("0x[[:xdigit:]]+")]
    HexInt(&'t str),

    // contains e or . => Number, otherwise => Int
    #[regex(r"-?([\d][\d|_]*|[\d][\d|_]*\.[\d|_]*|[\d|_]*\.[\d][\d|_]*)(e(-|\+)?[\d|_]+)?")]
    Number(&'t str),

    #[regex(r#"'.'|'\\x.{1,8}'|'\\[trn"\\]'"#)]
    Char(&'t str),

    #[regex(r#""([^"\\\x00-\x1F]|\\(["\\bnfrt/]|u[a-fA-F0-9]{4}))*""#)]
    String(&'t str),

    #[regex("\"\"\"", |lex| lex_raw_string(lex))]
    RawString(&'t str),

    #[regex(r"--[^\n]*", priority = 100)]
    LineComment(&'t str),

    #[token("{-", |lex| lex_block_comment(lex))]
    BlockComment(&'t str),

    #[regex("\\s*\n\\s*", lex_indent, priority = 12)]
    Indent(usize),

    LayBegin,
    LayEnd,
    LaySep,
    LayTop,
}

#[derive(Eq, PartialEq, Clone, Copy, Debug)]
#[allow(clippy::enum_variant_names)]
enum Delim {
    LytRoot,
    LytModuleDecl,
    LytTopDecl,
    LytTopDeclHead,
    LytDeclGuard,
    LytCase,
    LytCaseBinders,
    LytCaseGuard,
    LytLambdaBinders,
    LytParen,
    LytBrace,
    LytSquare,
    LytIf,
    LytThen,
    LytProperty,
    LytForall,
    LytTick,
    LytLet,
    LytLetStmt,
    LytWhere,
    LytOf,
    LytDo,
    LytAdo,
}

impl Delim {
    fn is_indented(&self) -> bool {
        use Delim::*;
        matches!(
            self,
            LytLet | LytLetStmt | LytWhere | LytOf | LytDo | LytAdo
        )
    }
}

pub fn lex(content: &str, fi: Fi) -> Vec<SourceToken<'_>> {
    let mut indent = 0;
    let mut state = vec![((0, 0), Delim::LytRoot), ((0, 0), Delim::LytWhere)];
    let mut out = Vec::new();
    let toks = Token::lexer(content)
        .spanned()
        .filter(|(t, _)| !matches!(t, Ok(Token::LineComment(_) | Token::BlockComment(_))))
        .map(|(t, r)| {
            if t.is_err() {
                return (t, r);
            }
            (
                Ok(match t.unwrap() {
                    Token::SymbolOrParen("(") => Token::LeftParen,
                    Token::SymbolOrParen(sym) => Token::Symbol(sym),

                    Token::Op("<-") => Token::LeftArrow,
                    Token::Op("->") => Token::RightArrow,
                    Token::Op("=>") => Token::RightFatArrow,
                    Token::Op("|") => Token::Pipe,
                    Token::Op("\\") => Token::Slash,
                    Token::Op("::") => Token::ColonColon,
                    Token::Op("@") => Token::At,
                    Token::Op("=") => Token::Equals,
                    x => x,
                }),
                r,
            )
        })
        .collect::<Vec<_>>();

    let mut scanned_to = 0;
    let mut line = 0;
    for (i, (t, s)) in toks.iter().enumerate() {
        let line_after = line + content[scanned_to..s.end].matches('\n').count();
        scanned_to = s.end;

        let span = Span::Known(
            fi,
            (line as usize, (s.start - indent) as usize),
            (line_after as usize, (s.end - indent) as usize),
        );
        match t {
            Ok(Token::Indent(at)) => {
                // We need to know the indentation of every token - even if there are tokens before it.
                indent = s.end.saturating_sub(*at);
            }
            Ok(tt) => {
                let next = match toks.get(i + 1) {
                    Some((Ok(Token::Indent(at)), _)) => (*at, line + 1),
                    // This is a crude approximation - but it's good enough for the Layout
                    // algorithm
                    _ => (s.end - indent, line),
                };

                // println!("{:?} {:?}", tt, state);
                let mut c = C {
                    t: *tt,
                    at: (s.start - indent, line),
                    next,
                    s: span,
                    state,
                    out: Vec::new(),
                };
                process(&mut c);
                state = c.state;
                for t in c.out {
                    out.push(t);
                }
            }
            Err(_) => {
                out.push((*t, span));
            }
        }
        line = line_after;
    }
    let last_span = Span::Known(fi, (line as usize, 0), (line as usize, 0));
    for (s, d) in state.iter() {
        if d.is_indented() && *s != (0, 0) {
            out.push((Ok(Token::LayEnd), last_span));
        }
    }
    out.push((Ok(Token::LayTop), last_span));
    out
}

pub type SourceToken<'t> = (Result<Token<'t>, ()>, Span);

#[derive(Clone)]
struct C<'t> {
    t: Token<'t>,
    s: Span,
    at: (usize, usize),
    next: (usize, usize),
    state: Vec<((usize, usize), Delim)>,
    // We clone this a but - but it's fine since it's usually small (< 3 elements)
    out: Vec<SourceToken<'t>>,
}

impl<'t> C<'t> {
    fn is_top(&self) -> bool {
        // NOTE[et]: The original Haskell code is slightly different here - since the lexer keeps track
        // of if it's lexing the `header` or the `body`.
        self.at.0 == 0
    }

    fn src(&self) -> SourceToken<'t> {
        (Ok(self.t), self.s)
    }

    fn pushStack(&mut self, t: (usize, usize), d: Delim) {
        self.state.push((t, d))
    }

    fn popStack(&mut self) {
        self.state.pop();
    }

    fn popIf<P>(&mut self, p: P)
    where
        P: Fn(Delim) -> bool,
    {
        if let Some((_, d)) = self.state.last() {
            if p(*d) {
                self.state.pop();
            }
        }
    }

    fn app(&mut self, o: SourceToken<'t>) {
        self.out.push(o)
    }

    fn appSrc(&mut self) {
        let s = self.src();
        self.app(s);
    }

    fn app_(&mut self, t: Token<'t>, s: Span) {
        self.app((Ok(t), s))
    }

    fn head(&self) -> ((usize, usize), Delim) {
        *self.state.last().unwrap_or(&((0, 0), Delim::LytRoot))
    }

    fn head2(&self) -> (Option<Delim>, Option<Delim>) {
        match self.state.len() {
            0 => (None, None),
            1 => (self.state.last().map(|x| x.1), None),
            _ => (
                self.state.last().map(|x| x.1),
                self.state.get(self.state.len() - 2).map(|x| x.1),
            ),
        }
    }

    fn default(&mut self) {
        let col = self.at.0;
        self.collapse(|i, d| d.is_indented() && col < i.0);
        self.insertSep();
        self.appSrc();
    }

    fn collapse<P>(&mut self, p: P)
    where
        P: Fn((usize, usize), Delim) -> bool,
    {
        while let Some((a, b)) = self.state.last() {
            if !p(*a, *b) {
                break;
            }
            if b.is_indented() {
                self.app_(Token::LayEnd, self.s);
            }
            self.popStack();
        }
    }

    fn insertStart(&mut self, d: Delim) {
        match self.state.iter().rev().find(|(_, x)| x.is_indented()) {
            Some((pos, _)) if self.next.0 <= pos.0 => (),
            _ => {
                self.pushStack(self.next, d);
                self.app_(Token::LayBegin, self.s);
            }
        }
    }

    fn insertEnd(&mut self) {
        self.app_(Token::LayEnd, self.s)
    }

    fn insertSep(&mut self) {
        use Delim::*;
        let sepP = |(x, y): (usize, usize)| -> bool { x == self.at.0 && y != self.at.1 };
        let indentSepP = |p: (usize, usize), d: Delim| -> bool { d.is_indented() && sepP(p) };
        match self.head() {
            (p, LytTopDeclHead | LytTopDecl) if sepP(p) => {
                self.popStack();
                self.app_(Token::LayTop, self.s);
            }
            (p, lyt) if indentSepP(p, lyt) => {
                self.app_(
                    if self.at.0 == 0 {
                        Token::LayTop
                    } else {
                        Token::LaySep
                    },
                    self.s,
                );
                if lyt == LytOf {
                    self.pushStack(self.at, LytCaseBinders);
                }
            }
            _ => (),
        }
    }
}

fn process(c: &mut C<'_>) {
    use Delim::*;
    use Token::*;
    let col = c.at.0;

    let offsideEndP = |i: (usize, usize), d: Delim| -> bool { d.is_indented() && col <= i.0 };

    let whereP = |i: (usize, usize), d: Delim| -> bool { d == LytDo || offsideEndP(i, d) };

    let indentedP = |_: (usize, usize), d: Delim| -> bool { d.is_indented() };

    let offsideP = |i: (usize, usize), d: Delim| -> bool { d.is_indented() && col < i.0 };

    let inP = |_: (usize, usize), d: Delim| -> bool {
        match d {
            LytLet => false,
            LytAdo => false,
            _ => d.is_indented(),
        }
    };

    match c.t {
        Lower("module") => {
            if c.is_top() {
                c.pushStack(c.at, LytModuleDecl);
            }
            c.default();
        }
        Lower("data") => {
            c.default();
            if c.is_top() {
                c.pushStack(c.at, LytTopDecl);
            } else {
                c.popIf(|x| matches!(x, LytProperty));
            }
        }
        Lower("class") => {
            c.default();
            if c.is_top() {
                c.pushStack(c.at, LytTopDeclHead);
            } else {
                c.popIf(|x| matches!(x, LytProperty));
            }
        }
        Where => match c.head() {
            (_, LytTopDeclHead) => {
                c.popStack();
                c.appSrc();
                c.insertStart(LytWhere);
            }
            (_, LytProperty) => {
                c.popStack();
                c.appSrc();
            }
            (_, LytModuleDecl) => {
                c.popStack();
                c.appSrc();
            }
            _ => {
                c.collapse(whereP);
                c.appSrc();
                c.insertStart(LytWhere);
            }
        },
        Lower("in") => {
            c.collapse(inP);
            match c.head2() {
                (Some(LytLetStmt), Some(LytAdo)) => {
                    c.popStack();
                    c.popStack();
                    c.insertEnd();
                    c.insertEnd();
                    c.appSrc();
                }
                (Some(lyt), _) if lyt.is_indented() => {
                    c.popStack();
                    c.insertEnd();
                    c.appSrc();
                }
                _ => {
                    c.default();
                    c.popIf(|x| matches!(x, LytProperty));
                }
            }
        }

        Let => {
            c.default();
            match c.head() {
                (_, LytProperty) => {
                    c.popStack();
                }
                //////////
                (p, LytDo | LytAdo) if p.0 == c.at.0 => c.insertStart(LytLetStmt),
                _ => c.insertStart(LytLet),
            }
        }

        Do => {
            c.default();
            match c.head() {
                (_, LytProperty) => {
                    c.popStack();
                }
                //////////
                _ => c.insertStart(LytDo),
            }
        }
        Ado => {
            c.default();
            match c.head() {
                (_, LytProperty) => {
                    c.popStack();
                }
                //////////
                _ => c.insertStart(LytAdo),
            }
        }

        Case => {
            c.default();
            match c.head() {
                (_, LytProperty) => {
                    c.popStack();
                }
                //////////
                _ => c.pushStack(c.at, LytCase),
            }
        }
        Of => {
            c.collapse(indentedP);
            match c.head() {
                (_, LytCase) => {
                    c.popStack();
                    c.appSrc();
                    c.insertStart(LytOf);
                    c.pushStack(c.next, LytCaseBinders);
                }
                _ => {
                    c.default();
                    c.popIf(|x| matches!(x, LytProperty));
                }
            }
        }

        If => {
            c.default();
            match c.head() {
                (_, LytProperty) => {
                    c.popStack();
                }
                //////////
                _ => c.pushStack(c.next, LytIf),
            }
        }
        Then => {
            let mut cc = c.clone();
            cc.collapse(indentedP);
            match cc.head() {
                (_, LytIf) => {
                    c.collapse(indentedP);
                    c.popStack();
                    c.appSrc();
                    c.pushStack(c.next, LytThen);
                }
                //////////
                _ => {
                    c.default();
                    c.popIf(|x| matches!(x, LytProperty));
                }
            }
        }
        Else => {
            let mut cc = c.clone();
            cc.collapse(indentedP);
            match cc.head() {
                (_, LytThen) => {
                    c.collapse(indentedP);
                    c.popStack();
                    c.appSrc();
                }
                _ => {
                    c.collapse(offsideP);
                    if c.is_top() {
                        c.insertSep();
                        c.appSrc();
                    } else {
                        c.insertSep();
                        c.appSrc();
                        c.popIf(|x| matches!(x, LytProperty));
                    }
                }
            }
        }

        Lower("forall") => {
            match c.head() {
                (_, LytIf) => {
                    c.popStack();
                    c.appSrc();
                    c.pushStack(c.next, LytThen);
                }
                //////////
                _ => {
                    c.default();
                    c.pushStack(c.next, LytForall);
                }
            }
        }

        Slash => {
            c.default();
            c.pushStack(c.next, LytLambdaBinders);
        }

        RightArrow => {
            let arrowP = |p: (usize, usize), d: Delim| -> bool {
                match d {
                    LytDo => true,
                    LytOf => false,
                    _ => offsideEndP(p, d),
                }
            };
            c.collapse(arrowP);
            let guardP = |d: Delim| -> bool {
                matches!(d, LytCaseBinders | LytCaseGuard | LytLambdaBinders)
            };
            c.popIf(guardP);
            c.appSrc();
        }

        Equals => {
            let equalsP = |_: (usize, usize), d: Delim| -> bool {
                matches!(d, LytWhere | LytLet | LytLetStmt)
            };
            let mut cc = c.clone();
            cc.collapse(equalsP);
            match cc.head() {
                (_, LytDeclGuard) => {
                    c.collapse(equalsP);
                    c.popStack();
                    c.appSrc();
                }
                _ => {
                    c.default();
                }
            };
        }

        Pipe => {
            let mut cc = c.clone();
            cc.collapse(offsideEndP);
            match cc.head() {
                (_, LytOf) => {
                    c.collapse(offsideEndP);
                    c.pushStack(c.next, LytCaseGuard);
                    c.appSrc();
                }
                (_, LytLet) => {
                    c.collapse(offsideEndP);
                    c.pushStack(c.next, LytDeclGuard);
                    c.appSrc();
                }
                (_, LytLetStmt) => {
                    c.collapse(offsideEndP);
                    c.pushStack(c.next, LytDeclGuard);
                    c.appSrc();
                }
                (_, LytWhere) => {
                    c.collapse(offsideEndP);
                    c.pushStack(c.next, LytDeclGuard);
                    c.appSrc();
                }
                _ => c.default(),
            }
        }

        Tick => {
            let mut cc = c.clone();
            cc.collapse(indentedP);
            match cc.head() {
                (_, LytTick) => {
                    c.collapse(indentedP);
                    c.popStack();
                    c.appSrc();
                }
                _ => {
                    c.collapse(offsideEndP);
                    c.insertSep();
                    c.appSrc();
                    c.pushStack(c.next, LytTick);
                }
            }
        }

        Comma => {
            c.collapse(indentedP);
            match c.head() {
                (_, LytBrace) => {
                    c.appSrc();
                    c.pushStack(c.next, LytProperty);
                }
                _ => {
                    c.appSrc();
                }
            };
        }

        Op(".") => {
            c.default();
            match c.head() {
                (_, LytForall) => {
                    c.popStack();
                }
                _ => {
                    c.pushStack(c.at, LytProperty);
                }
            }
        }

        LeftParen => {
            c.default();
            c.pushStack(c.at, LytParen);
        }
        LeftBrace => {
            c.default();
            c.pushStack(c.at, LytBrace);
            c.pushStack(c.at, LytProperty);
        }
        LeftSquare => {
            c.default();
            c.pushStack(c.at, LytSquare);
        }
        RightParen => {
            c.collapse(indentedP);
            c.popIf(|x| matches!(x, LytParen));
            c.appSrc();
        }
        RightBrace => {
            c.collapse(indentedP);
            c.popIf(|x| matches!(x, LytProperty));
            c.popIf(|x| matches!(x, LytBrace));
            c.appSrc();
        }
        RightSquare => {
            c.collapse(indentedP);
            c.popIf(|x| matches!(x, LytSquare));
            c.appSrc();
        }

        String(_) | RawString(_) => {
            c.default();
            c.popIf(|x| matches!(x, LytProperty));
        }

        Lower(_) => {
            c.default();
            c.popIf(|x| matches!(x, LytProperty));
        }

        Op(_) => {
            c.collapse(offsideEndP);
            c.insertSep();
            c.appSrc();
        }

        _ => {
            c.default();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;

    fn p(s: &'static str) -> String {
        lex(s, Fi(0))
            .iter()
            .map(|x| format!("{:?}", x.0))
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn empty_string() {
        assert_snapshot!(p(""));
    }

    #[test]
    fn some_tokens() {
        assert_snapshot!(p("module A where (a, b, c)\nimport B as B\nfoo = 1 + B.t"));
    }

    #[test]
    fn lower() {
        assert_snapshot!(p("variable"));
    }

    #[test]
    fn string() {
        assert_snapshot!(p(r#""I like pie""#))
    }

    #[test]
    fn string_with_quote() {
        assert_snapshot!(p(r#""Qotes are \"rad\"""#))
    }

    #[test]
    fn raw_string_6() {
        assert_snapshot!(p("\"\"\"\"\"\""))
    }

    #[test]
    fn raw_string_7() {
        assert_snapshot!(p("\"\"\"\"\"\"\""))
    }

    #[test]
    fn raw_string_8() {
        assert_snapshot!(p("\"\"\"\"\"\"\"\""))
    }

    #[test]
    fn escaped_backslash() {
        assert_snapshot!(p(r#""\\""#))
    }

    #[test]
    fn int_0() {
        assert_snapshot!(p("123"))
    }

    #[test]
    fn int_1() {
        assert_snapshot!(p("1_111_1"))
    }

    #[test]
    fn int_2() {
        assert_snapshot!(p("0xFEE"))
    }

    #[test]
    fn number_0() {
        assert_snapshot!(p("12.3"))
    }

    #[test]
    fn number_1() {
        assert_snapshot!(p("1e+10"))
    }

    #[test]
    fn number_2() {
        assert_snapshot!(p("1e+10"))
    }

    #[test]
    fn line_comment() {
        assert_snapshot!(p("a + -- this is a comment\nb"))
    }

    #[test]
    fn block_comment() {
        assert_snapshot!(p("a + {- this\n is\n a\n comment\n -} b"))
    }

    #[test]
    fn block_comment2() {
        assert_snapshot!(p("a +{- this\n is\n a\n comment\n -}b"))
    }

    #[test]
    fn op() {
        assert_snapshot!(p("<#>"))
    }

    #[test]
    fn symbol() {
        assert_snapshot!(p("(<#>)"))
    }

    #[test]
    fn hole() {
        assert_snapshot!(p("a = ?foo 1 2"))
    }

    #[test]
    fn forall() {
        assert_snapshot!(p("forall f. Monad f => f a -> f Unit"))
    }

    #[test]
    fn upper() {
        assert_snapshot!(p("Unit"))
    }

    #[test]
    fn qual() {
        assert_snapshot!(p("A.B.Unit A.B.var A.B.### A.B...."))
    }

    #[test]
    fn lower_with_single_quote() {
        assert_snapshot!(p("myFunction'"))
    }

    #[test]
    fn funky_string() {
        assert_snapshot!(p("\"\""))
    }

    #[test]
    fn char_dash() {
        assert_snapshot!(p("'-'"))
    }

    #[test]
    fn char_a() {
        assert_snapshot!(p("'A'"))
    }

    #[test]
    fn char_hex() {
        assert_snapshot!(p(r"'\x00'"))
    }

    #[test]
    fn simple_int() {
        assert_snapshot!(p(r"1"))
    }

    #[test]
    fn simple_number() {
        assert_snapshot!(p(r"1.0"))
    }

    #[test]
    fn symbol_paren_plus() {
        assert_snapshot!(p("(+)"))
    }

    #[test]
    fn symbol_paren_minus() {
        assert_snapshot!(p("(-)"))
    }

    #[test]
    fn this_wacky_thing_is_an_opperator() {
        assert_snapshot!(p("¤"))
    }

    #[test]
    fn some_char_special_cases() {
        assert_snapshot!(p(r#"'\n''\r''\t''\"''\\''\xF00'"#))
    }

    #[test]
    fn symbol_minus() {
        assert_snapshot!(p("-"))
    }

    #[test]
    fn swedish_lower() {
        assert_snapshot!(p("överförning"))
    }

    #[test]
    fn swedish_upper() {
        assert_snapshot!(p("Överförning"))
    }

    #[test]
    fn knows_if_start_of_line() {
        assert_snapshot!(p(r#"
import A as A

foo :: Int
foo = bar + baz
        "#))
    }

    #[test]
    fn tricky_do_notation() {
        assert_snapshot!(p(r#"
f = 
    do
        do
            a <- f b
            do
                x <- y
        e v

foo = bar + baz
        "#))
    }

    #[test]
    fn leaking_where() {
        assert_snapshot!(p(r#"
module A where

instance A A where
  f = F

a :: A
a = 1
        "#))
    }

    #[test]
    fn weird_comments() {
        assert_snapshot!(p(r#"
            -- comment
            --+ comment
            --| comment
            --# comment
            --@@@@ comment
        "#))
    }
}
