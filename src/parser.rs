#![allow(clippy::needless_lifetimes)]

use papaya::HashMap;

use crate::ast::*;
use crate::lexer::Token as T;
use crate::lexer::Token;

macro_rules! b {
    ($e:expr) => {
        Box::new($e)
    };
}

macro_rules! t {
    ($name:ident, $token:ident, $thing:ident) => {
        fn $name(p: &mut P<'_>) -> Option<$thing> {
            match p.next() {
                (Some(T::$token(x)), s) => Some($thing(S(p.intern(x), s))),
                _ => p.raise_(stringify!($thing)),
            }
        }
    };
}

t!(name, Lower, Name);
t!(proper, Upper, ProperName);
t!(number, Number, Number);
t!(hex_int, HexInt, HexInt);
t!(char, Char, Char);
t!(op, Op, Op);
t!(hole, Hole, Hole);

fn symbol(p: &mut P<'_>) -> Option<Symbol> {
    match p.next() {
        (Some(T::Symbol(x)), s) => Some(Symbol(S(p.intern(&x[1..x.len() - 1]), s))),
        _ => p.raise_(stringify!(Symbol)),
    }
}

fn mname(p: &mut P<'_>) -> Option<MName> {
    match p.peek2t() {
        (Some(T::Qual(q)), Some(T::Upper(u))) => {
            let ud = p.intern(&format!("{}{}", q, u));
            let s = p.span();
            p.skip();
            let s = s.merge(p.span());
            p.skip();
            Some(MName(S(ud, s)))
        }
        (Some(T::Upper(u)), _) => {
            let ud = p.intern(u);
            let s = p.span();
            p.skip();
            Some(MName(S(ud, s)))
        }
        _ => None,
    }
}

fn qual(p: &mut P<'_>) -> Option<Qual> {
    match p.next() {
        (Some(T::Qual(x)), s) => Some(Qual(S(p.intern(&x[0..(x.len() - 1)]), s.trim_end()))),
        _ => p.raise_(stringify!($thing)),
    }
}

fn boolean(p: &mut P<'_>) -> Option<Boolean> {
    match p.next() {
        (Some(T::Lower(x @ ("true" | "false"))), s) => Some(Boolean(S(p.intern(x), s))),
        _ => p.raise_("Boolean"),
    }
}

fn string(p: &mut P<'_>) -> Option<Str> {
    match p.next() {
        (Some(T::String(x) | T::RawString(x)), s) => Some(Str(S(p.intern(x), s))),
        _ => p.raise_("String | RawString"),
    }
}

fn label_no_eat(p: &mut P<'_>) -> Option<Label> {
    Some(match p.peek() {
        (Some(T::Lower(n) | T::String(n) | T::RawString(n)), s) => Label(S(p.intern(n), s)),
        _ => return None,
    })
}

fn label(p: &mut P<'_>) -> Option<Label> {
    let out = label_no_eat(p)?;
    p.skip();
    Some(out)
}

macro_rules! kw {
    ($name:ident, $kw:pat) => {
        fn $name(p: &mut P) -> Option<()> {
            p.expect(|x| matches!(x, $kw), stringify!($kw))
        }
    };
}

kw!(kw_lp, T::LeftParen);
kw!(kw_rp, T::RightParen);
kw!(kw_lb, T::LeftBrace);
kw!(kw_rb, T::RightBrace);
kw!(kw_ls, T::LeftSquare);
kw!(kw_rs, T::RightSquare);
kw!(kw_left_arrow, T::LeftArrow);
kw!(kw_right_arrow, T::RightArrow);
kw!(kw_right_imply, T::RightFatArrow);
kw!(kw_coloncolon, T::ColonColon);
kw!(kw_colon, T::Op(":"));
kw!(kw_tick, T::Tick);
kw!(kw_comma, T::Comma);

kw!(kw_left_imply, T::Op("<="));
kw!(kw_at, T::At);
kw!(kw_pipe, T::Pipe);
kw!(kw_dot, T::Op("."));
kw!(kw_eq, T::Equals);
kw!(kw_underscore, T::Lower("_"));
kw!(kw_minus, T::Op("-"));
kw!(kw_backslash, T::Slash);

kw!(kw_module, T::Lower("module"));
kw!(kw_where, T::Where);
kw!(kw_class, T::Lower("class"));
kw!(kw_as, T::Lower("as"));
kw!(kw_import, T::Lower("import"));
kw!(kw_foreign, T::Foreign);
kw!(kw_hiding, T::Lower("hiding"));
kw!(kw_type, T::Lower("type"));
kw!(kw_role, T::Lower("role"));
kw!(kw_nominal, T::Lower("nominal"));
kw!(kw_representational, T::Lower("representational"));
kw!(kw_phantom, T::Lower("phantom"));
kw!(kw_newtype, T::Newtype);
kw!(kw_derive, T::Derive);
kw!(kw_data, T::Lower("data"));
kw!(kw_forall, T::Lower("forall"));
kw!(kw_let, T::Let);
kw!(kw_in, T::Lower("in"));
kw!(kw_if, T::If);
kw!(kw_then, T::Then);
kw!(kw_else, T::Else);
kw!(kw_instance, T::Instance);
kw!(kw_case, T::Case);
kw!(kw_of, T::Of);
kw!(kw_do, T::Do);
kw!(kw_ado, T::Ado);

kw!(kw_begin, T::LayBegin);
kw!(kw_end, T::LayEnd);
kw!(kw_sep, T::LaySep);
kw!(kw_top, T::LayTop);

macro_rules! q {
    ($name:ident, $inner:expr, $token:expr, $thing:ident) => {
        fn $name(p: &mut P<'_>) -> Option<$thing> {
            let q = if matches!(p.peekt(), Some(T::Qual(_))) {
                Some(qual(p)?)
            } else {
                None
            };
            let x = $inner(p)?;
            Some($token(q, x))
        }
    };
}

q!(qname, name, QName, QName);
q!(qproper, proper, QProperName, QProperName);
q!(qsymbol, symbol, QSymbol, QSymbol);
q!(qop, op, QOp, QOp);

pub fn module<'t>(p: &mut P<'t>) -> Option<Module> {
    let h = header(p);
    let mut ds = Vec::new();
    loop {
        if !p.skip_until(|x| matches!(x, T::LayTop)) {
            break;
        }

        while matches!(p.peekt(), Some(T::LayTop)) {
            kw_top(p)?;
        }

        if p.peekt().is_none() {
            break;
        }

        let start = p.span();
        let i = p.i;
        let e = p.errors.len();

        let failed = if let Some(out) = decl(p) {
            ds.push(out);
            false
        } else {
            true
        };
        p.recover();

        let before_skip = p.i;
        if !p.skip_until(|x| matches!(x, T::LayTop)) {
            break;
        }
        let after_skip = p.i;

        if before_skip != after_skip {
            p.raise(Serror::FailedToParseDecl(
                start,
                p.errors.len() - e,
                before_skip,
                after_skip,
            ));
        } else if p.errors.len() != e || failed {
            p.raise(Serror::FailedToParseDecl(
                start,
                p.errors.len() - e,
                i,
                after_skip,
            ));
        }
    }
    Some(Module(h, ds))
}

fn header<'t>(p: &mut P<'t>) -> Option<Header> {
    while matches!(p.peek().0, Some(T::LayTop)) {
        kw_top(p)?;
    }
    let m = p.span();
    kw_module(p)?;
    let name = mname(p)?;
    let exports = exports(p);
    p.recover();
    let w = p.span();
    kw_where(p)?;
    if matches!(p.peekt(), Some(T::LayBegin)) {
        p.skip();
    }
    let imports = imports(p);
    Some(Header(name, exports, imports, m, w))
}

// TODO: pick the errros from the branch that moved the most consumed tokens
// TODO: Check some tokens first and then commit to a path?
macro_rules! ttry {
    ($p:ident, $t:expr) => {{
        let mut p_ = $p.fork();
        if let Some(out) = $t(&mut p_) {
            $p.i = p_.i;
            Some(out)
        } else {
            None
        }
    }};
}

macro_rules! alt {
    ($p:ident: $e:expr, $($t:expr),*) => {
        {
            let (i_, x, errs) = (|| {
                let mut errs = Vec::new();
                errs.push($e);
            $(
                if let (p_, Some(out)) = {
                    let mut p_ = $p.fork();
                    let out = $t(&mut p_);
                    for err in p_.errors.into_iter() {
                        errs.push(err)
                    }
                    (p_.i, out)
                } { return (p_, Some(out), Vec::new()) }
                errs.push($e);
            )*
                ($p.i, None, errs)
            })();

            $p.i = i_;

            for err in errs.into_iter() {
                $p.errors.push(err)
            }
            x
        }
    };
    ($p:ident: $e:expr, $($t:expr),* ,) => { alt!($p: $e, $($t),*) };
}

macro_rules! next_is {
    ($p:pat) => {
        |p: &mut P<'t>| matches!(p.peekt(), Some($p))
    };
}

macro_rules! next_isnt {
    ($p:pat) => {
        |p: &mut P<'t>| !matches!(p.peekt(), Some($p))
    };
}

fn many<'t, FE, E>(p: &mut P<'t>, _: &'static str, e: FE) -> Vec<E>
where
    FE: Fn(&mut P<'t>) -> Option<E>,
{
    let mut out = Vec::new();
    while let Some(ee) = e(p) {
        out.push(ee);
    }
    out
}

fn many_until<'t, FE, FF, E>(p: &mut P<'t>, _: &'static str, e: FE, f: FF) -> Vec<E>
where
    FE: Fn(&mut P<'t>) -> Option<E>,
    FF: Fn(&mut P<'t>) -> bool,
{
    let mut out = Vec::new();
    while let Some(ee) = if !f(p) { e(p) } else { None } {
        out.push(ee);
    }
    out
}

fn sep<'t, FS, FE, E, S>(p: &mut P<'t>, _: &'static str, s: FS, e: FE) -> Vec<E>
where
    FS: Fn(&mut P<'t>) -> Option<S>,
    FE: Fn(&mut P<'t>) -> Option<E>,
{
    let mut out = Vec::new();
    loop {
        if let Some(ee) = e(p) {
            out.push(ee);
        } else {
            break;
        }
        if ttry!(p, s).is_some() {
            continue;
        } else {
            break;
        }
    }
    out
}

fn sep_until<'t, FS, FE, FF, E, S>(p: &mut P<'t>, _: &'static str, s: FS, e: FE, f: FF) -> Vec<E>
where
    FS: Fn(&mut P<'t>) -> Option<S>,
    FE: Fn(&mut P<'t>) -> Option<E>,
    FF: Fn(&mut P<'t>) -> bool,
{
    let mut out = Vec::new();
    while !f(p) {
        if let Some(ee) = e(p) {
            out.push(ee);
        } else {
            break;
        }
        if f(p) {
            break;
        }
        if s(p).is_some() {
            continue;
        } else {
            break;
        }
    }
    out
}

fn sep_until_<'t, FE, E>(p: &mut P<'t>, _: &'static str, e: FE) -> Option<Vec<E>>
where
    FE: Fn(&mut P<'t>) -> Option<E>,
{
    kw_begin(p)?;
    let mut out = Vec::new();
    while !next_is!(T::LayEnd)(p) {
        while next_is!(T::LaySep)(p) {
            kw_sep(p)?;
        }
        if let Some(ee) = e(p) {
            out.push(ee);
        } else {
            break;
        }
        if !next_is!(T::LaySep)(p) {
            break;
        }
        kw_sep(p)?;
    }
    kw_end(p)?;
    Some(out)
}

fn exports<'t>(p: &mut P<'t>) -> Option<Vec<Export>> {
    if matches!(p.peekt(), Some(T::LeftParen)) {
        kw_lp(p);
        let exports = sep_until(p, "export", kw_comma, export, next_is!(T::RightParen));
        kw_rp(p);
        Some(exports)
    } else {
        None
    }
}

fn export<'t>(p: &mut P<'t>) -> Option<Export> {
    alt!(
        p: Serror::Info(p.span(), "export"),
        |p: &mut _| {
            kw_type(p)?;
            Some(Export::TypSymbol(symbol(p)?))
        },
        |p: &mut _| {
            kw_class(p)?;
            Some(Export::Class(proper(p)?))
        },
        |p: &mut _| {
            kw_module(p)?;
            Some(Export::Module(mname(p)?))
        },
        |p: &mut _| { Some(Export::Value(name(p)?)) },
        |p: &mut _| { Some(Export::Symbol(symbol(p)?)) },
        |p: &mut _| {
            let n = proper(p)?;
            let ms = data_members(p)?;
            Some(Export::TypDat(n, ms))
        },
        |p: &mut _| { Some(Export::Typ(proper(p)?)) }
    )
}

fn data_members<'t>(p: &mut P<'t>) -> Option<DataMember> {
    if next_is!(T::Symbol("(..)"))(p) {
        let s = p.span();
        p.skip();
        return Some(DataMember::All(s));
    }

    kw_lp(p)?;
    let out = match p.peek().0 {
        Some(T::RightParen) => DataMember::Some(Vec::new()),
        Some(_) => DataMember::Some(sep_until(
            p,
            "data_member.proper",
            kw_comma,
            proper,
            next_is!(T::RightParen),
        )),
        _ => p.raise_("Illegal data members")?,
    };
    kw_rp(p)?;
    Some(out)
}

fn imports<'t>(p: &mut P<'t>) -> Vec<ImportDecl> {
    let mut out = Vec::new();
    while matches!(p.peek2t(), (Some(T::LayTop), Some(T::Lower("import")))) {
        p.skip();
        if let Some(import) = import_decl(p) {
            out.push(import);
        }
        p.recover();
        p.skip_until(|t| matches!(t, T::LayTop));
    }
    out
}

fn import_decl<'t>(p: &mut P<'t>) -> Option<ImportDecl> {
    let start = p.span();
    kw_import(p)?;
    let from = mname(p)?;
    // NOTE: import A hiding (a) (a) - is a syntax error
    let (hiding, names) = if next_is!(T::Lower("hiding"))(p) {
        kw_hiding(p)?;
        kw_lp(p)?;
        let hiding = sep_until(
            p,
            "hiding imports",
            kw_comma,
            import,
            next_is!(T::RightParen),
        );
        kw_rp(p)?;
        (hiding, Vec::new())
    } else if next_is!(T::LeftParen)(p) {
        kw_lp(p)?;
        let names = sep_until(p, "imports", kw_comma, import, next_is!(T::RightParen));
        kw_rp(p)?;
        (Vec::new(), names)
    } else {
        (Vec::new(), Vec::new())
    };
    let to = if next_is!(T::Lower("as"))(p) {
        kw_as(p)?;
        Some(mname(p)?)
    } else {
        None
    };
    Some(ImportDecl {
        start,
        from,
        hiding,
        names,
        to,
    })
}

fn import<'t>(p: &mut P<'t>) -> Option<Import> {
    alt!(
        p: Serror::Info(p.span(), "import"),
        |p: &mut _| {
            kw_type(p)?;
            Some(Import::TypSymbol(symbol(p)?))
        },
        |p: &mut _| {
            kw_class(p)?;
            Some(Import::Class(proper(p)?))
        },
        |p: &mut _| { Some(Import::Value(name(p)?)) },
        |p: &mut _| { Some(Import::Symbol(symbol(p)?)) },
        |p: &mut _| {
            let n = proper(p)?;
            let ms = data_members(p)?;
            Some(Import::TypDat(n, ms))
        },
        |p: &mut _| { Some(Import::Typ(proper(p)?)) }
    )
}

fn typ_atom<'t>(p: &mut P<'t>, err: Option<&'static str>) -> Option<Typ> {
    match p.peek2t() {
        (Some(T::Lower("_")), _) => {
            let span = p.span();
            kw_underscore(p)?;
            Some(Typ::Wildcard(span))
        }
        (Some(T::Lower(_)), _) => Some(Typ::Var(name(p)?)),
        (Some(T::Upper(_)), _) | (Some(T::Qual(_)), Some(T::Upper(_))) => {
            Some(Typ::Constructor(qproper(p)?))
        }
        (Some(T::Symbol(_)), _) | (Some(T::Qual(_)), Some(T::Symbol(_))) => {
            Some(Typ::Symbol(qsymbol(p)?))
        }

        (Some(T::String(_) | T::RawString(_)), _) => Some(Typ::Str(string(p)?)),
        (Some(T::Number(n)), _) if n.parse::<i32>().is_ok() => {
            let span = p.span();
            number(p);
            Some(Typ::Int(false, Int(S(n.parse::<i32>().unwrap(), span))))
        }
        // (Some(T::_), _) => { Some(Typ::Int(int(p)?)) },
        (Some(T::Hole(_)), _) => Some(Typ::Hole(hole(p)?)),
        (Some(T::LeftBrace), _) => {
            let start = p.span();
            kw_lb(p)?;
            let r = row(p)?;
            kw_rb(p)?;
            let end = p.span();
            Some(Typ::Record(S(r, start.merge(end))))
        }
        // NOTE: ( a :: B ) is considered a row-type in this conflict
        (Some(T::LeftParen), _) => {
            let start = p.span();
            kw_lp(p)?;
            alt!(
                p: Serror::Info(p.span(), "row or paren"),
                |p: &mut P<'t>| {
                    let r = row(p)?;
                    kw_rp(p)?;
                    let end = p.span();
                    Some(Typ::Row(S(r, start.merge(end))))
                },
                |p: &mut P<'t>| {
                    let r = typ(p)?;
                    kw_rp(p)?;
                    Some(Typ::Paren(b!(r)))
                },
            )
        }
        _ => {
            if let Some(err) = err {
                p.raise(Serror::Unexpected(p.span(), p.peekt(), err));
                None
                // NOTE[et]: This causes an infinet loop.
                // Some(Typ::Error(p.span()))
            } else {
                None
            }
        }
    }
}

// Higher binds tighter
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Prec {
    L(usize),
    R(usize),
}

impl Prec {
    fn zero() -> usize {
        0
    }

    fn next(&self, current: usize) -> Option<usize> {
        match (current, self) {
            (s, Self::L(o)) if o > &s => Some(s + 1),
            (s, Self::R(o)) if o > &s => Some(s + 1),
            (s, Self::R(o)) if o == &s => Some(s),
            _ => None,
        }
    }

    fn prec(&self) -> usize {
        match self {
            Self::L(a) | Self::R(a) => *a,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum TypOp {
    Kind,
    Arr,
    FatArr,
    Op(QOp),
    App,
}

fn typ_op<'t>(p: &mut P<'t>) -> Option<TypOp> {
    match p.peek2t() {
        (Some(T::ColonColon), _) => {
            kw_coloncolon(p)?;
            Some(TypOp::Kind)
        }
        (Some(T::RightArrow), _) => {
            kw_right_arrow(p)?;
            Some(TypOp::Arr)
        }
        (Some(T::RightFatArrow), _) => {
            kw_right_imply(p)?;
            Some(TypOp::FatArr)
        }
        // Not a type op
        (Some(T::Op("<=")), _) => None,
        (Some(T::Qual(_)), Some(T::Op(_))) | (Some(T::Op(_)), _) => Some(TypOp::Op(qop(p)?)),
        _ => {
            if matches!(typ_atom(&mut p.fork(), None)?, Typ::Error(_)) {
                None
            } else {
                Some(TypOp::App)
            }
        }
    }
}

fn typ_fop(t: &TypOp) -> Prec {
    use Prec::*;
    match t {
        TypOp::Kind => L(0),
        TypOp::FatArr => R(1),
        TypOp::Arr => R(1),
        // This is not right - we can maybe do better
        TypOp::Op(_) => L(3),
        TypOp::App => L(4),
    }
}

fn typ_mrg(p: &mut P<'_>, op: TypOp, lhs: Typ, rhs: Typ) -> Typ {
    match op {
        TypOp::Kind => Typ::Kinded(b!(lhs), b!(rhs)),
        TypOp::Arr => Typ::Arr(b!(lhs), b!(rhs)),
        TypOp::FatArr => {
            if let Some(lhs) = lhs.clone().cast_to_constraint() {
                Typ::Constrained(lhs, b!(rhs))
            } else {
                p.raise(Serror::NotAConstraint(lhs.span()));
                Typ::Arr(b!(lhs), b!(rhs))
            }
        }
        TypOp::Op(op) => Typ::Op(b!(lhs), op, b!(rhs)),
        TypOp::App => Typ::App(b!(lhs), b!(rhs)),
    }
}

fn top_typ<'t>(p: &mut P<'t>) -> Option<Typ> {
    if next_is!(T::Lower("forall"))(p) {
        kw_forall(p)?;
        let vars = typ_var_bindings(p);
        kw_dot(p)?;
        let inner = typ(p)?;
        Some(Typ::Forall(vars, b!(inner)))
    } else {
        typ_atom(p, Some("Expected a typ"))
    }
}

fn typ<'t>(p: &mut P<'t>) -> Option<Typ> {
    let lhs = top_typ(p)?;
    pratt_typ(p, lhs, Prec::zero())
}

fn pratt_typ<'t>(p: &mut P<'t>, mut lhs: Typ, prec: usize) -> Option<Typ> {
    while let Some(outer_lookahead) = (|p: &mut P<'t>| {
        let op = typ_op(&mut p.fork())?;
        if typ_fop(&op).prec() >= prec {
            if !matches!(op, TypOp::App) {
                let _ = typ_op(p)?;
            }
            Some(op)
        } else {
            None
        }
    })(p)
    {
        // Make the check a peek
        let mut rhs = top_typ(p)?;
        while let Some(next) = (|p: &mut P<'t>| {
            let op = typ_op(&mut p.fork())?;
            typ_fop(&op).next(typ_fop(&outer_lookahead).prec())
        })(p)
        {
            rhs = pratt_typ(p, rhs, next)?;
        }
        lhs = typ_mrg(p, outer_lookahead, lhs, rhs);
    }
    Some(lhs)
}

fn typ_only_call<'t>(p: &mut P<'t>) -> Option<Typ> {
    let mut lhs = top_typ(p)?;
    loop {
        let mut pp = p.fork();
        let rhs = typ_atom(&mut pp, Some("Expected a type"));
        if let Some(rhs) = rhs {
            lhs = Typ::App(b!(lhs), b!(rhs));
            *p = pp;
        } else {
            break;
        }
    }
    Some(lhs)
}

fn typ_var_binding<'t>(p: &mut P<'t>) -> Option<TypVarBinding> {
    let is_paren = matches!(p.peekt(), Some(T::LeftParen));
    if is_paren {
        kw_lp(p)?;
    }

    let is_at = matches!(p.peekt(), Some(T::At));
    if is_at {
        kw_at(p)?;
    }
    let name = name(p)?;
    let ty = if matches!(p.peekt(), Some(T::ColonColon)) {
        kw_coloncolon(p)?;
        typ(p)
    } else {
        None
    };
    if is_paren {
        kw_rp(p)?;
    }
    Some(TypVarBinding(name, ty, is_at))
}

fn typ_var_bindings<'t>(p: &mut P<'t>) -> Vec<TypVarBinding> {
    many_until(
        p,
        "typ_var_bindings",
        typ_var_binding,
        next_isnt!(T::LeftParen | T::At | T::Lower(_)),
    )
}

fn simple_typ_var_bindings<'t>(p: &mut P<'t>) -> Vec<TypVarBinding> {
    let vars = typ_var_bindings(p);
    for v in vars.iter() {
        if v.2 {
            p.raise(Serror::NotSimpleTypeVarBinding(v.0 .0 .1))
        }
    }
    vars
}

fn row_label<'t>(p: &mut P<'t>) -> Option<(Label, Typ)> {
    let l = label(p)?;
    kw_coloncolon(p)?;
    let t = typ(p)?;
    Some((l, t))
}

fn row<'t>(p: &mut P<'t>) -> Option<Row> {
    let c = sep_until(
        p,
        "row",
        kw_comma,
        row_label,
        next_isnt!(T::Comma | T::Lower(_) | T::String(_) | T::RawString(_)),
    );

    let x = if matches!(p.peekt(), Some(T::Pipe)) {
        kw_pipe(p)?;
        typ(p).map(|x| b!(x))
    } else {
        None
    };

    Some(Row(c, x))
}

#[derive(Debug, Eq, PartialEq)]
enum ExprOp {
    Op(QOp),
    Infix(Expr),
    App,
}

fn expr_op<'t>(p: &mut P<'t>) -> Option<ExprOp> {
    match p.peek2t() {
        (Some(T::Qual(_)), Some(T::Op(_))) | (Some(T::Op(_)), _) => Some(ExprOp::Op(qop(p)?)),
        (Some(T::Tick), _) => {
            kw_tick(p)?;
            let e = expr(p)?;
            kw_tick(p)?;
            Some(ExprOp::Infix(e))
        }
        _ => {
            if matches!(expr_atom(p, None)?, Expr::Error(_)) {
                None
            } else {
                Some(ExprOp::App)
            }
        }
    }
}

fn expr_fop(t: &ExprOp) -> Prec {
    use Prec::*;
    match t {
        // NOTE[et]: With more information we can get the correct precedences
        ExprOp::Op(_) => R(1),
        ExprOp::Infix(_) => L(2),
        ExprOp::App => L(3),
    }
}

fn expr_mrg(op: ExprOp, lhs: Expr, rhs: Expr) -> Expr {
    match op {
        ExprOp::Op(op) => Expr::Op(b!(lhs), op, b!(rhs)),
        ExprOp::Infix(op) => Expr::Infix(b!(lhs), b!(op), b!(rhs)),
        ExprOp::App => Expr::App(b!(lhs), b!(rhs)),
    }
}

fn expr<'t>(p: &mut P<'t>) -> Option<Expr> {
    let lhs = expr_atom(p, Some("Expected an expression"))?;
    let e = pratt_expr(p, lhs, Prec::zero())?;
    Some(if matches!(p.peekt(), Some(T::ColonColon)) {
        kw_coloncolon(p)?;
        let t = typ(p)?;
        Expr::Typed(b!(e), t)
    } else {
        e
    })
}

fn expr_where<'t>(p: &mut P<'t>) -> Option<Expr> {
    let e = expr(p)?;
    if matches!(p.peekt(), Some(T::Where)) {
        let start = p.span();
        kw_where(p)?;
        let b = sep_until_(p, "where-bindings", let_binding)?;
        Some(Expr::Where(start, b!(e), b))
    } else {
        Some(e)
    }
}

fn pratt_expr<'t>(p: &mut P<'t>, mut lhs: Expr, prec: usize) -> Option<Expr> {
    while let Some(outer_lookahead) = (|p: &mut P<'t>| {
        let op = expr_op(&mut p.fork())?;
        if expr_fop(&op).prec() >= prec {
            if !matches!(op, ExprOp::App) {
                let _ = expr_op(p)?;
            }
            Some(op)
        } else {
            None
        }
    })(p)
    {
        let mut rhs = expr_atom(p, Some("Expected an expression after the operator"))?;
        while let Some(next) = (|p: &mut P<'t>| {
            let op = expr_op(&mut p.fork())?;
            expr_fop(&op).next(expr_fop(&outer_lookahead).prec())
        })(p)
        {
            let i = p.i;
            rhs = pratt_expr(p, rhs, next)?;
            assert_ne!(i, p.i, "STUCK EXPR!");
        }
        let should_break = matches!(rhs, Expr::Error(_));
        lhs = expr_mrg(outer_lookahead, lhs, rhs);
        if should_break {
            break;
        }
    }
    Some(lhs)
}

fn expr_atom<'t>(p: &mut P<'t>, err: Option<&'static str>) -> Option<Expr> {
    let e = match p.peek2t() {
        (Some(T::Op("-")), _) => {
            kw_minus(p)?;
            Some(Expr::Negate(b!(expr_atom(p, err)?)))
        }
        (Some(T::Where), _) => return None,
        (Some(T::Lower("true" | "false")), _) => Some(Expr::Boolean(boolean(p)?)),
        (Some(T::If), _) => {
            let start = p.span();
            kw_if(p)?;
            let a = b!(expr(p)?);
            kw_then(p)?;
            let b = b!(expr(p)?);
            kw_else(p)?;
            let c = b!(expr(p)?);
            Some(Expr::IfThenElse(start, a, b, c))
        }
        (Some(T::Let), _) => {
            let start = p.span();
            kw_let(p)?;
            // Handle inline ones?
            let b = sep_until_(p, "let-bindings", let_binding)?;
            kw_in(p)?;
            let e = b!(expr(p)?);
            Some(Expr::Let(start, b, e))
        }
        (Some(T::Qual(_)), Some(T::Ado)) | (Some(T::Ado), _) => {
            let q = if matches!(p.peekt(), Some(T::Qual(_))) {
                Some(qual(p)?)
            } else {
                None
            };
            kw_ado(p)?;
            let ds = sep_until_(p, "ado-block", do_statement)?;
            kw_in(p)?;
            let e = expr(p)?;
            Some(Expr::Ado(q, ds, b!(e)))
        }
        (Some(T::Qual(_)), Some(T::Do)) | (Some(T::Do), _) => {
            let q = if matches!(p.peekt(), Some(T::Qual(_))) {
                Some(qual(p)?)
            } else {
                None
            };
            kw_do(p)?;
            let ds = sep_until_(p, "do-block", do_statement)?;
            Some(Expr::Do(q, ds))
        }
        (Some(T::Slash), _) => {
            let start = p.span();
            kw_backslash(p)?;
            let binders = many_until(p, "lambda binder", binder_no_type, next_is!(T::RightArrow));
            kw_right_arrow(p)?;
            let body = b!(expr(p)?);
            Some(Expr::Lambda(start, binders, body))
        }
        (Some(T::Case), _) => {
            let start = p.span();
            kw_case(p)?;
            let xs = sep_until(p, "case expr", kw_comma, expr, next_is!(T::Of));
            kw_of(p)?;
            let branches = sep_until_(p, "case branch", case_branch)?;
            Some(Expr::Case(start, xs, branches))
        }
        (Some(T::Lower("_")), _) => {
            let start = p.span();
            kw_underscore(p)?;
            Some(Expr::Section(start))
        }
        (Some(T::Hole(_)), _) => Some(Expr::Hole(hole(p)?)),
        (Some(T::Lower(_)), _) | (Some(T::Qual(_)), Some(T::Lower(_))) => {
            Some(Expr::Ident(qname(p)?))
        }
        (Some(T::Upper(_)), _) | (Some(T::Qual(_)), Some(T::Upper(_))) => {
            Some(Expr::Constructor(qproper(p)?))
        }
        (Some(T::Symbol(_)), _) | (Some(T::Qual(_)), Some(T::Symbol(_))) => {
            Some(Expr::Symbol(qsymbol(p)?))
        }
        (Some(T::Char(_)), _) => Some(Expr::Char(char(p)?)),
        (Some(T::String(_) | T::RawString(_)), _) => Some(Expr::Str(string(p)?)),
        (Some(T::Number(_)), _) => Some(Expr::Number(number(p)?)),
        (Some(T::HexInt(_)), _) => Some(Expr::HexInt(hex_int(p)?)),
        (Some(T::LeftSquare), _) => {
            let start = p.span();
            kw_ls(p)?;
            let inner = sep_until(p, "array expr", kw_comma, expr, next_is!(T::RightSquare));
            kw_rs(p)?;
            let end = p.span();
            Some(Expr::Array(start, inner, end))
        }
        (Some(T::LeftBrace), _) => {
            let start = p.span();
            kw_lb(p)?;
            let inner = sep_until(
                p,
                "record expr",
                kw_comma,
                record_label,
                next_is!(T::RightBrace),
            );
            kw_rb(p)?;
            let end = p.span();
            Some(Expr::Record(start, inner, end))
        }
        (Some(T::LeftParen), _) => {
            kw_lp(p)?;
            let inner = expr(p)?;
            kw_rp(p)?;
            Some(Expr::Paren(b!(inner)))
        }
        _ => {
            // Not a valid start of an expression - but that isn't nessecarily an error
            return if let Some(err) = err {
                p.raise(Serror::Unexpected(p.span(), p.peekt(), err));
                Some(Expr::Error(p.span()))
            } else {
                None
            };
        }
    };
    let mut e = if let Some(e) = e {
        e
    } else {
        return p.raise_("Invalid expression");
    };

    if let Some(labels) = {
        if matches!(p.peekt(), Some(T::Op("."))) {
            let mut out = Vec::new();
            while matches!(p.peekt(), Some(T::Op("."))) {
                kw_dot(p)?;
                out.push(label(p)?);
            }
            Some(out)
        } else {
            None
        }
    } {
        e = Expr::Access(b!(e), labels);
    }

    if let Some(x) = if matches!(p.peekt(), Some(T::LeftBrace)) {
        ttry!(p, record_updates)
    } else {
        None
    } {
        e = Expr::Update(b!(e), x);
    }

    while let Some(labels) = if matches!(p.peekt(), Some(T::At)) {
        kw_at(p)?;
        Some(typ_atom(p, Some("Expected type for VTA"))?)
    } else {
        None
    } {
        e = Expr::Vta(b!(e), labels);
    }
    Some(e)
}

fn do_statement<'t>(p: &mut P<'t>) -> Option<DoStmt> {
    while next_is!(T::LaySep)(p) {
        kw_sep(p)?;
    }
    alt!(p: Serror::Info(p.span(), "do_statement"),
        |p: &mut P<'t>| {
            if next_is!(T::Lower("in"))(p) {
                Some(None)
            } else {
                None
            }
        },
        |p: &mut P<'t>| {
            let b = binder(p)?;
            kw_left_arrow(p)?;
            let e = expr(p)?;
            Some(Some(DoStmt::Stmt(Some(b), e)))
        },
        |p: &mut P<'t>| {
            let e = expr(p)?;
            Some(Some(DoStmt::Stmt(None, e)))
        },
        |p: &mut P<'t>| {
            kw_let(p)?;
            // Handle inline ones?
            let b = sep_until_(p, "let-bindings", let_binding)?;
            Some(Some(DoStmt::Let(b)))
        },
    )?
}

fn let_binding<'t>(p: &mut P<'t>) -> Option<LetBinding> {
    alt!(p: Serror::Info(p.span(), "let_binding"),
        // NOTE[et]: Binder conflicts with both of these - fun
        |p: &mut P<'t>| {
            let n = name(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(LetBinding::Sig(n, t))
        },
        |p: &mut P<'t>| {
            let n = name(p)?;
            let bs = many(p, "let-binder", |x| binder_atom(x, None));
            let decl = guarded_decl(p)?;
            Some(LetBinding::Name(n, bs, decl))
        },
        |p: &mut P<'t>| {
            let b = binder(p)?;
            kw_eq(p)?;
            let e = expr_where(p)?;
            Some(LetBinding::Pattern(b, e))
        },
    )
}

fn binder<'t>(p: &mut P<'t>) -> Option<Binder> {
    let b = binder_no_type(p)?;
    if matches!(p.peekt(), Some(T::ColonColon)) {
        kw_coloncolon(p)?;
        let t = typ(p)?;
        Some(Binder::Typed(b!(b), t))
    } else {
        Some(b)
    }
}

fn binder_no_type<'t>(p: &mut P<'t>) -> Option<Binder> {
    let mut lhs = binder_call(p)?;
    while matches!(
        p.peek2t(),
        (Some(T::Op(_)), _) | (Some(T::Qual(_)), Some(T::Op(_)))
    ) {
        let op = qop(p)?;
        let rhs = binder_call(p)?;
        lhs = Binder::Op(b!(lhs), op, b!(rhs));
    }
    Some(lhs)
}

fn binder_call<'t>(p: &mut P<'t>) -> Option<Binder> {
    let head = binder_atom(p, Some("Expected a binder"))?;
    if matches!(head, Binder::Constructor(_)) {
        let bs = many(p, "binder_no_type", |x| binder_atom(x, None));
        let bs = [vec![head], bs].concat();
        match Binder::to_constructor(bs) {
            Ok(a) => Some(a),
            Err(e) => p.raise_(e),
        }
    } else {
        Some(head)
    }
}

fn binder_atom<'t>(p: &mut P<'t>, err: Option<&'static str>) -> Option<Binder> {
    match p.peek2t() {
        (Some(T::Lower("_")), _) => {
            let start = p.span();
            kw_underscore(p)?;
            Some(Binder::Wildcard(start))
        }
        (Some(T::Lower("true" | "false")), _) => Some(Binder::Boolean(boolean(p)?)),
        (Some(T::Lower(_)), _) => {
            let n = name(p)?;
            if matches!(p.peekt(), Some(T::At)) {
                kw_at(p)?;
                let t = binder_atom(p, Some("Expected binder atom after @"))?;
                Some(Binder::Named(n, b!(t)))
            } else {
                Some(Binder::Var(n))
            }
        }
        (Some(T::Upper(_)), _) | (Some(T::Qual(_)), _) => Some(Binder::Constructor(qproper(p)?)),
        (Some(T::Char(_)), _) => Some(Binder::Char(char(p)?)),
        (Some(T::String(_) | T::RawString(_)), _) => Some(Binder::Str(string(p)?)),
        (Some(T::Op("-")), _) => {
            kw_minus(p)?;
            Some(Binder::Number(true, number(p)?))
        }
        (Some(T::Number(_)), _) => Some(Binder::Number(false, number(p)?)),
        (Some(T::LeftSquare), _) => {
            kw_ls(p)?;
            let bs = sep_until(
                p,
                "array binder",
                kw_comma,
                binder,
                next_is!(T::RightSquare),
            );
            kw_rs(p)?;
            Some(Binder::Array(bs))
        }
        (Some(T::LeftBrace), _) => {
            kw_lb(p)?;
            let bs = sep_until(
                p,
                "record binder",
                kw_comma,
                record_binder,
                next_is!(T::RightBrace),
            );
            kw_rb(p)?;
            Some(Binder::Record(bs))
        }
        (Some(T::LeftParen), _) => {
            kw_lp(p)?;
            let b = b!(binder(p)?);
            kw_rp(p)?;
            Some(Binder::Paren(b))
        }
        _ => {
            if let Some(err) = err {
                p.raise_(err)
            } else {
                None
            }
        }
    }
}

fn record_binder<'t>(p: &mut P<'t>) -> Option<RecordLabelBinder> {
    if matches!(p.peek2t(), (_, Some(T::Op(":")))) {
        let f = label(p)?;
        kw_colon(p)?;
        let e = binder(p)?;
        Some(RecordLabelBinder::Field(f, e))
    } else {
        Some(RecordLabelBinder::Pun(name(p)?))
    }
}

fn guarded_decl<'t>(p: &mut P<'t>) -> Option<GuardedExpr> {
    if matches!(p.peekt(), Some(T::Equals)) {
        kw_eq(p)?;
        Some(GuardedExpr::Unconditional(expr_where(p)?))
    } else {
        let decls = many(p, "guardDeclExpr", guarded_decl_expr);
        if decls.is_empty() {
            p.raise_("Not a valid declaration - expected a `=`")
        } else {
            Some(GuardedExpr::Guarded(decls))
        }
    }
}

fn guarded_decl_expr<'t>(p: &mut P<'t>) -> Option<(Vec<Guard>, Expr)> {
    if !matches!(p.peekt(), Some(T::Pipe)) {
        return None;
    }
    kw_pipe(p)?;
    let gs = sep(p, "guard", kw_comma, guard_statement);
    kw_eq(p)?;
    let e = expr_where(p)?;
    Some((gs, e))
}

fn guard_statement<'t>(p: &mut P<'t>) -> Option<Guard> {
    alt!(p: Serror::Info(p.span(), "guard statements"),
        |p: &mut P<'t>| {
            let b = binder(p)?;
            kw_left_arrow(p)?;
            let e = expr(p)?;
            Some(Guard::Binder(b, e))
        },
        |p: &mut P<'t>| {
            Some(Guard::Expr(expr(p)?))
        },
    )
}

fn record_label<'t>(p: &mut P<'t>) -> Option<RecordLabelExpr> {
    if matches!(p.peek2t(), (_, Some(T::Op(":")))) {
        let f = label(p)?;
        kw_colon(p)?;
        let e = expr(p)?;
        Some(RecordLabelExpr::Field(f, e))
    } else {
        Some(RecordLabelExpr::Pun(name(p)?))
    }
}

fn record_updates<'t>(p: &mut P<'t>) -> Option<Vec<RecordUpdate>> {
    kw_lb(p)?;
    let updates = sep_until(
        p,
        "record_updates",
        kw_comma,
        record_update,
        next_is!(T::RightBrace),
    );
    kw_rb(p)?;
    Some(updates)
}

fn record_update<'t>(p: &mut P<'t>) -> Option<RecordUpdate> {
    let f = label_no_eat(p)?;
    if !matches!(p.peek2t(), (Some(_), Some(T::Equals | T::LeftBrace))) {
        return None;
    }
    p.next();
    if next_is!(T::Equals)(p) {
        kw_eq(p)?;
    }

    alt!(p: Serror::Info(p.span(), "record_label"),
        |p: &mut P<'t>| {
            Some(RecordUpdate::Leaf(f, expr(p)?))
        },
        |p: &mut P<'t>| {
            Some(RecordUpdate::Branch(f, record_updates(p)?))
        },
    )
}

fn case_branch<'t>(p: &mut P<'t>) -> Option<CaseBranch> {
    let bs = sep(p, "case_branch", kw_comma, binder_no_type);
    let x = if matches!(p.peekt(), Some(T::RightArrow)) {
        kw_right_arrow(p)?;
        GuardedExpr::Unconditional(expr_where(p)?)
    } else {
        kw_pipe(p)?;
        GuardedExpr::Guarded(sep_until(
            p,
            "guarded_case",
            kw_pipe,
            guarded_case_expr,
            next_is!(T::LaySep | T::LayEnd),
        ))
    };
    Some(CaseBranch(bs, x))
}

fn guarded_case_expr<'t>(p: &mut P<'t>) -> Option<(Vec<Guard>, Expr)> {
    let gs = sep_until(
        p,
        "guard",
        kw_comma,
        guard_statement,
        next_is!(T::RightArrow),
    );
    kw_right_arrow(p)?;
    let e = expr_where(p)?;
    Some((gs, e))
}

pub fn decl<'t>(p: &mut P<'t>) -> Option<Decl> {
    match p.peek3t() {
        (Some(T::Lower("data")), _, Some(T::ColonColon)) => {
            kw_data(p)?;
            let name = proper(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::DataKind(name, t))
        }
        (Some(T::Lower("data")), _, _) => {
            kw_data(p)?;
            let name = proper(p)?;
            let vars = simple_typ_var_bindings(p);
            let enums = if next_is!(T::Equals)(p) {
                kw_eq(p)?;
                sep_until(p, "data-decl", kw_pipe, data_cnstr, next_is!(T::LayTop))
            } else {
                Vec::new()
            };
            Some(Decl::Data(name, vars, enums))
        }

        (Some(T::Lower("type")), Some(T::Lower("role")), _) => {
            kw_type(p)?;
            kw_role(p)?;
            let name = proper(p)?;
            let roles = many_until(p, "roles", role, next_is!(T::LayTop));
            Some(Decl::Role(name, roles))
        }
        (Some(T::Lower("type")), _, Some(T::ColonColon)) => {
            kw_type(p)?;
            let name = proper(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::TypeKind(name, t))
        }
        (Some(T::Lower("type")), _, _) => {
            kw_type(p)?;
            let name = proper(p)?;
            let vars = simple_typ_var_bindings(p);
            kw_eq(p)?;
            let ty = typ(p)?;
            Some(Decl::Type(name, vars, ty))
        }

        (Some(T::Newtype), _, Some(T::ColonColon)) => {
            kw_newtype(p)?;
            let name = proper(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::NewTypeKind(name, t))
        }
        (Some(T::Newtype), _, _) => {
            kw_newtype(p)?;
            let name = proper(p)?;
            let vars = simple_typ_var_bindings(p);
            kw_eq(p)?;
            let ctrc = proper(p)?;
            let t = typ(p)?;
            Some(Decl::NewType(name, vars, ctrc, t))
        }

        (Some(T::Lower("class")), _, Some(T::ColonColon)) => {
            kw_class(p)?;
            let name = proper(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::ClassKind(name, t))
        }
        (Some(T::Lower("class")), _, _) => {
            kw_class(p)?;
            let cs = constraints(p, true);
            let name = proper(p)?;
            let vars = simple_typ_var_bindings(p);
            let deps = fundeps(p)?;
            let mem = members(p)?;
            Some(Decl::Class(cs, name, vars, deps, mem))
        }

        (Some(T::Else), Some(T::Instance), _) | (Some(T::Instance), _, _) => {
            let is_else = if matches!(p.peekt(), Some(T::Else)) {
                kw_else(p)?;
                true
            } else {
                false
            };
            kw_instance(p)?;
            let head = instance_head(p)?;

            let bs = if next_is!(T::Where)(p) {
                kw_where(p)?;
                // NOTE[et]: This might need to be more graciouse
                sep_until_(p, "inst_bindings", inst_binding)?
            } else {
                Vec::new()
            };

            Some(Decl::Instance(is_else, head, bs))
        }

        (Some(T::Derive), _, _) => {
            kw_derive(p)?;
            let is_newtype = if matches!(p.peekt(), Some(T::Newtype)) {
                kw_newtype(p)?;
                true
            } else {
                false
            };
            kw_instance(p)?;

            let head = instance_head(p)?;

            Some(Decl::Derive(is_newtype, head))
        }

        // NOTE: "data" is a "name" => It's placed earlier in the parser
        (Some(T::Foreign), Some(T::Lower("import")), Some(T::Lower("data"))) => {
            kw_foreign(p)?;
            kw_import(p)?;
            kw_data(p)?;

            let n = proper(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::ForeignData(n, t))
        }
        (Some(T::Foreign), Some(T::Lower("import")), Some(_)) => {
            kw_foreign(p)?;
            kw_import(p)?;

            let n = name(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::Foreign(n, t))
        }

        (Some(T::Infixr) | Some(T::Infixl) | Some(T::Infix), _, _) => {
            let start = p.span();
            let f = S(
                match p.peekt() {
                    Some(T::Infixr) => Some(FixitySide::R),
                    Some(T::Infixl) => Some(FixitySide::L),
                    Some(T::Infix) => Some(FixitySide::C),
                    _ => p.raise_("Expected fixity"),
                }?,
                start,
            );
            p.skip();
            // TODO: This has to be an int
            let i = number(p)?;

            Some(match p.peekt() {
                Some(T::Lower("type")) => {
                    kw_type(p)?;
                    let x = typ_atom(p, Some("Expected a type"))?;
                    kw_as(p)?;
                    let o = op(p)?;
                    Decl::FixityTyp(f, i, x, o)
                }
                _ => {
                    let x = expr_atom(p, Some("Expected an expression"))?;
                    kw_as(p)?;
                    let o = op(p)?;
                    Decl::Fixity(f, i, x, o)
                }
            })
        }

        (Some(T::Lower(_)), Some(T::ColonColon), _) => {
            let n = name(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(Decl::Sig(n, t))
        }
        (Some(T::Lower(_)), _, _) => {
            let n = name(p)?;
            let bs = many(p, "binders", |x| binder_atom(x, None));
            let decl = guarded_decl(p)?;
            Some(Decl::Def(n, bs, decl))
        }
        _ => p.raise_("Not a valid top-level declaration"),
    }
}

fn role(p: &mut P<'_>) -> Option<S<Role>> {
    let start = p.span();
    let d = alt!(p: Serror::Info(start, "role"),
            |p: &mut P<'_>| {
                kw_nominal(p)?;
                Some(Role::Nominal)
            },
            |p: &mut P<'_>| {
                kw_representational(p)?;
                Some(Role::Representational)
            },
            |p: &mut P<'_>| {
                kw_phantom(p)?;
                Some(Role::Phantom)
            },
    )?;
    Some(S(d, start))
}

fn instance_head<'t>(p: &mut P<'t>) -> Option<InstHead> {
    if next_is!(T::Lower(_))(p) {
        name(p)?;
        kw_coloncolon(p)?;
    }
    let cs = constraints(p, false);
    let n = qproper(p)?;
    let bs = many(p, "instance head", |p| typ_atom(p, None));
    Some(InstHead(cs, n, bs))
}

fn inst_binding<'t>(p: &mut P<'t>) -> Option<InstBinding> {
    alt!(p: Serror::Info(p.span(), "inst_binding"),
        |p: &mut P<'t>| {
            let n = name(p)?;
            kw_coloncolon(p)?;
            let t = typ(p)?;
            Some(InstBinding::Sig(n, t))
        },
        |p: &mut P<'t>| {
            let n = name(p)?;
            let bs = many(p, "inst-binder", |x| binder_atom(x, None));
            let decl = guarded_decl(p)?;
            Some(InstBinding::Def(n, bs, decl))
        },
    )
}

fn data_cnstr<'t>(p: &mut P<'t>) -> Option<(ProperName, Vec<Typ>)> {
    let n = proper(p)?;
    let ts = many_until(p, "data cnstr", typ, next_is!(T::Pipe | T::LayTop));
    Some((n, ts))
}

fn constraints<'t>(p: &mut P<'t>, l: bool) -> Option<Vec<Constraint>> {
    alt!(p: Serror::Info(p.span(), "constraints"),
        |p: &mut P<'t>| {
            kw_lp(p)?;
            let cs = sep_until(p, "constraints-sep", kw_comma, typ, next_is!(T::RightParen))
                .into_iter()
                .map(|x| x.cast_to_constraint())
                .collect::<Option<Vec<_>>>()?;
            kw_rp(p)?;
            if l {
                kw_left_imply(p)?;
            } else {
                kw_right_imply(p)?;
            }
            Some(Some(cs))
        },
        |p: &mut P<'t>| {
            // NOTE: There's just parsing conflicts everywhere :(
            let t = typ_only_call(p)?.cast_to_constraint()?;
            if l {
                kw_left_imply(p)?;
            } else {
                kw_right_imply(p)?;
            }
            Some(Some(vec![t]))
        },
        |_: &mut P<'t>| {
            Some(None::<Vec<Constraint>>)
        }
    )?
}

fn fundeps<'t>(p: &mut P<'t>) -> Option<Option<Vec<FunDep>>> {
    if next_is!(T::Pipe)(p) {
        kw_pipe(p)?;
        let mut deps = Vec::new();
        loop {
            deps.push(fundep(p)?);
            if next_is!(T::Comma)(p) {
                kw_comma(p)?;
            } else {
                break;
            }
        }
        Some(Some(deps))
    } else {
        Some(None::<Vec<FunDep>>)
    }
}

fn fundep<'t>(p: &mut P<'t>) -> Option<FunDep> {
    if next_is!(T::RightArrow)(p) {
        kw_right_arrow(p)?;
        Some(FunDep(Vec::new(), many(p, "fundep A", name)))
    } else {
        let b = many_until(p, "fundep B", name, next_isnt!(T::Lower(_)));
        kw_right_arrow(p)?;
        let c = many_until(p, "fundep C", name, next_isnt!(T::Lower(_)));
        Some(FunDep(b, c))
    }
}

fn members<'t>(p: &mut P<'t>) -> Option<Vec<ClassMember>> {
    if matches!(p.peekt(), Some(T::Where)) {
        kw_where(p)?;
        sep_until_(p, "members", member)
        // NOTE[et]: This might need to be more graciouse
    } else {
        Some(Vec::new())
    }
}

fn member<'t>(p: &mut P<'t>) -> Option<ClassMember> {
    let n = name(p)?;
    kw_coloncolon(p)?;
    let t = typ(p)?;
    Some(ClassMember(n, t))
}

#[derive(Clone, Copy, Debug)]
pub enum Serror<'s> {
    Info(Span, &'static str),
    Unexpected(Span, Option<Token<'s>>, &'static str),
    NotSimpleTypeVarBinding(Span),
    NotAConstraint(Span),
    NotAtEOF(Span, Option<Token<'s>>),
    FailedToParseDecl(Span, usize, usize, usize),
}

impl<'s> Serror<'s> {
    pub fn same_kind_of_error(&self, other: &Self) -> bool {
        match (self, other) {
            (Serror::Info(_, a), Serror::Info(_, b)) => a == b,
            (Serror::Unexpected(_, _, a), Serror::Unexpected(_, _, b)) => a == b,
            (Serror::NotSimpleTypeVarBinding(_), Serror::NotSimpleTypeVarBinding(_)) => true,
            (Serror::NotAConstraint(_), Serror::NotAConstraint(_)) => true,
            (Serror::NotAtEOF(_, _), Serror::NotAtEOF(_, _)) => true,
            (Serror::FailedToParseDecl(_, _, _, _), Serror::FailedToParseDecl(_, _, _, _)) => true,
            _ => false,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Serror::Info(a, _)
            | Serror::Unexpected(a, _, _)
            | Serror::NotSimpleTypeVarBinding(a)
            | Serror::NotAConstraint(a)
            | Serror::NotAtEOF(a, _)
            | Serror::FailedToParseDecl(a, _, _, _) => *a,
        }
    }
}

#[derive(Clone, Debug)]
pub struct P<'s> {
    pub i: usize,
    pub tokens: &'s Vec<(Result<Token<'s>, ()>, Span)>,
    pub errors: Vec<Serror<'s>>,
    pub panic: bool,
    pub steps: std::cell::RefCell<usize>,
    pub names: &'s HashMap<Ud, String>,
}

impl<'s> P<'s> {
    pub fn new(
        tokens: &'s Vec<(Result<Token<'s>, ()>, Span)>,
        names: &'s HashMap<Ud, String>,
    ) -> Self {
        Self {
            i: 0,
            steps: 0.into(),
            panic: false,
            errors: Vec::new(),
            tokens,
            names,
        }
    }

    fn intern(&self, s: &'_ str) -> Ud {
        let ud = Ud::new(s);
        self.names.pin().get_or_insert_with(ud, || s.into());
        ud
    }

    fn check_loop(&self) {
        *self.steps.borrow_mut() += 1;
        if *self.steps.borrow() > 1000 {
            panic!("Found loop in parser, {}\n{:?}", self.i, self.tokens)
        }
    }

    fn peek_(&self) -> (Option<Token<'s>>, Span) {
        self.check_loop();
        (self.tokens.get(self.i).and_then(|x| x.0.ok()), self.span())
    }

    fn peek(&self) -> (Option<Token<'s>>, Span) {
        if self.panic {
            (None, self.span())
        } else {
            self.peek_()
        }
    }

    fn peek2t(&self) -> (Option<Token<'s>>, Option<Token<'s>>) {
        self.check_loop();
        if self.panic {
            (None, None)
        } else {
            (
                self.tokens.get(self.i).and_then(|x| x.0.ok()),
                self.tokens.get(self.i + 1).and_then(|x| x.0.ok()),
            )
        }
    }

    fn peek3t(&self) -> (Option<Token<'s>>, Option<Token<'s>>, Option<Token<'s>>) {
        self.check_loop();
        if self.panic {
            (None, None, None)
        } else {
            (
                self.tokens.get(self.i).and_then(|x| x.0.ok()),
                self.tokens.get(self.i + 1).and_then(|x| x.0.ok()),
                self.tokens.get(self.i + 2).and_then(|x| x.0.ok()),
            )
        }
    }

    pub fn peekt(&self) -> Option<Token<'s>> {
        if self.panic {
            None
        } else {
            self.peek_().0
        }
    }

    fn next(&mut self) -> (Option<Token<'s>>, Span) {
        if self.panic {
            return (None, self.span());
        }
        let out = self.peek_();
        self.skip();
        out
    }

    pub fn span(&self) -> Span {
        self.tokens
            .get(self.i)
            .or_else(|| self.tokens.last())
            .map(|x| x.1)
            .unwrap_or(Span::Zero)
    }

    fn fork(&mut self) -> Self {
        self.check_loop();
        Self {
            i: self.i,
            tokens: self.tokens,
            errors: Vec::new(),
            panic: self.panic,
            steps: self.steps.clone(),
            names: self.names,
        }
    }

    fn skip(&mut self) {
        *self.steps.borrow_mut() = 0;
        self.i += 1;
        // NOTE: For now we skipp some of the tokens in this parser
        while matches!(self.peek_().0, Some(T::LineComment(_) | T::BlockComment(_))) {
            self.i += 1;
        }
    }

    fn recover(&mut self) {
        self.panic = false;
    }

    fn skip_until<F>(&mut self, f: F) -> bool
    where
        F: Fn(Token<'s>) -> bool,
    {
        loop {
            if self.i > self.tokens.len() {
                break;
            }
            if let (Some(x), _) = self.peek_() {
                if f(x) {
                    return true;
                }
            }
            self.skip();
        }
        false
    }

    fn expect<F>(&mut self, f: F, err: &'static str) -> Option<()>
    where
        F: Fn(Token<'s>) -> bool,
    {
        if let (Some(x), _) = self.peek() {
            if f(x) {
                self.next();
                return Some(());
            }
        }
        self.raise(Serror::Unexpected(self.span(), self.peekt(), err));
        None
    }

    fn raise_<A>(&mut self, err: &'static str) -> Option<A> {
        self.raise(Serror::Unexpected(self.span(), self.peekt(), err));
        None
    }

    fn raise(&mut self, err: Serror<'s>) {
        self.errors.push(err)
    }
}

#[cfg(test)]
mod tests {
    use insta::assert_snapshot;

    macro_rules! gen_parser {
        ($a:ident, $p:ident) => {
            pub fn $a(src: &str) -> String {
                use super::*;
                use crate::lexer;
                use std::io::BufWriter;

                let l = lexer::lex(&src, Fi(0));
                let d = papaya::HashMap::new();
                let mut p = P::new(&l, &d);

                let mut buf = BufWriter::new(Vec::new());
                $p(&mut p).show(0, &mut buf).unwrap();
                let inner = buf.into_inner().map_err(|x| format!("{:?}", x)).unwrap();

                format!(
                    "{} of {}\n===\n{}===\n{}",
                    p.i,
                    p.tokens.len(),
                    String::from_utf8(inner)
                        .map_err(|x| format!("{:?}", x))
                        .unwrap(),
                    p.errors
                        .iter()
                        .map(|x| format!("{:?}", x))
                        .collect::<Vec<_>>()
                        .join("\n")
                )
            }
        };
    }

    #[test]
    fn empty_string() {
        assert_snapshot!(p_module(""));
    }

    #[test]
    fn normal_definition() {
        assert_snapshot!(p_module("module A (a, b, c) where"));
    }

    #[test]
    fn everything_header() {
        assert_snapshot!(p_module(
            r#"
module A.B.C (a, class B, C, D(..), E(F, G), 
 (+), type (+), module H) where

import A
import A as A
import A.B.C as A.C
import A.B.C (a, class B, 
 C, D(..), E(F, G), (+), type (+))
import A.B.C hiding (foo)
        "#
        ));
    }

    fn p_import(s: &'static str) -> String {
        p_module(&format!("module Import where\n\n{}", s))
    }

    #[test]
    fn simple_joe_import() {
        assert_snapshot!(p_import("import Joe"))
    }

    #[test]
    fn simple_import() {
        assert_snapshot!(p_import("import A as A"))
    }

    #[test]
    fn import_with_newlines() {
        assert_snapshot!(p_import("import A (foo\n , bar\n , baz)"))
    }

    fn p_typ(s: &'static str) -> String {
        p_module(&format!("module Typ where\n\nf :: {}", s))
    }

    #[test]
    fn typ_empty_row() {
        assert_snapshot!(p_typ("()"))
    }

    #[test]
    fn typ_row_kind_ambiguity_row() {
        assert_snapshot!(p_typ("( a :: A )"))
    }

    #[test]
    fn typ_row_kind_ambiguity_typ() {
        assert_snapshot!(p_typ("A :: Type"))
    }

    #[test]
    fn typ_higher_kinded() {
        assert_snapshot!(p_typ("Foo bar biz"))
    }

    #[test]
    fn typ_a_signature() {
        assert_snapshot!(p_typ("forall a. Monoid a => a -> a -> a"))
    }

    #[test]
    fn typ_b_signature() {
        assert_snapshot!(p_typ("forall a b . Foo a b => Bar a b => b -> b"))
    }

    #[test]
    fn typ_b_simple_signature() {
        assert_snapshot!(p_typ("Foo => Bar => b -> b"))
    }

    #[test]
    fn typ_c_signature() {
        assert_snapshot!(p_typ(
            "
     forall out pkA pkB propsB rowB propsA rowA select
   . GetPk (C pkA N) propsA
  => ReflectArray pkA
  => HasMagicMapping rowA rowA
  => AllColumns rowA select
  => HasMagicSelect propsA rowA select select out
  => GetPk (C pkB N) propsB
  => ReflectArray pkB
  => HasMagicMapping rowB rowB
  => Table propsA rowA
  -> Table propsB rowB
  -> (Record out -> Record rowB)
  -> Sql Unit"
        ))
    }

    #[test]
    fn typ_operators() {
        assert_snapshot!(p_typ("Array $ Maybe $ Maybe $ Int"))
    }

    fn p_typ_var_binding(s: &'static str) -> String {
        p_module(&format!("module TypVar where\n\nf :: forall {}. Unit", s))
    }

    #[test]
    fn typ_var_bindings_a() {
        assert_snapshot!(p_typ("a"))
    }

    #[test]
    fn typ_var_bindings_a_at() {
        assert_snapshot!(p_typ_var_binding("@a"))
    }

    #[test]
    fn typ_var_bindings_a_at_paren() {
        assert_snapshot!(p_typ_var_binding("( @a )"))
    }

    #[test]
    fn typ_var_bindings_a_at_paren_kind() {
        assert_snapshot!(p_typ_var_binding("( @a :: Kind )"))
    }

    #[test]
    fn typ_app() {
        assert_snapshot!(p_typ("X.Z (A (B.C D)) E"))
    }

    #[test]
    fn typ_row() {
        assert_snapshot!(p_typ(" ( a :: {} , a :: {}) "))
    }

    fn p_expr(s: &'static str) -> String {
        p_module(&format!("module Expr where\n\nf = {}", s))
    }

    #[test]
    fn expr_simple() {
        assert_snapshot!(p_expr("1 + 1"))
    }

    #[test]
    fn expr_tick() {
        assert_snapshot!(p_expr("a `b` c"))
    }

    #[test]
    fn expr_messy() {
        assert_snapshot!(p_expr(
            "(1 + 1) * 2 + foo @A `a + b` A.B.C.d A.B.+ q :: Int"
        ))
    }

    #[test]
    fn expr_record() {
        assert_snapshot!(p_expr("{ a, b: 1 }"))
    }

    #[test]
    fn expr_record_construct() {
        assert_snapshot!(p_expr("foo { a : 1 }"))
    }

    #[test]
    fn expr_record_update() {
        assert_snapshot!(p_expr("foo { a = 1 }"))
    }

    #[test]
    fn expr_record_update_full() {
        assert_snapshot!(p_expr("foo { a = 1, b = { c = 1 }, d = { e: 1 } }"))
    }

    #[test]
    fn expr_if() {
        assert_snapshot!(p_expr("if a == 2 then b else c"))
    }

    #[test]
    fn expr_let() {
        assert_snapshot!(p_expr(
            r"
            let
                x = 1
            in 2
    "
        ))
    }

    #[test]
    fn expr_let_multiple() {
        assert_snapshot!(p_expr(
            r"
            let
                x = 1
                x = 1
                x = 1
            in 2
    "
        ))
    }

    #[test]
    fn expr_let_inline() {
        assert_snapshot!(p_expr(r"let x = 1 in 2"))
    }

    #[test]
    fn expr_case() {
        assert_snapshot!(p_expr(
            r"
        case 1 + 1 of
            2 -> foo
            3 | Just _ <- foo bar -> baz
                    where
                        baz = 3
        "
        ))
    }

    #[test]
    fn expr_do() {
        assert_snapshot!(p_expr(
            r"
        do
            a <- f 2
            b <- g a
            fazz 1 2
            let 
                a = 1
            pure (b + a)
        "
        ))
    }

    #[test]
    fn expr_ado() {
        assert_snapshot!(p_expr(
            r"
        ado
            a <- f 2
            b <- g a
            fazz 1 2
            in b + a
        "
        ))
    }

    #[test]
    fn expr_ado_b() {
        assert_snapshot!(p_expr(
            r" ado
                    a <- f 2
                    in a
            "
        ))
    }

    #[test]
    fn qualified_ado() {
        assert_snapshot!(p_expr(
            r" A.B.ado
                    a <- f 2
                    in a
            "
        ))
    }

    #[test]
    fn qualified_do() {
        assert_snapshot!(p_expr(
            r" A.B.do
                    foo bar
            "
        ))
    }

    gen_parser!(p_module, module);

    #[test]
    fn minimal_a() {
        assert_snapshot!(p_module(
            r"
module A.C (a) where

t :: T
t =
  T.d
    [ T.d
        let
          q a b =
            a
              { a: _.o
              , b: _.id
              , c
              , d: 1
              , e
              }

          q a b c =
            A
              { a:
                  case b of
                    true -> Nothing
                    false -> Just (page + 1)
              , b: b # c
              }

          q = a b []
        in \_ -> 123
    ]
            "
        ))
    }

    #[test]
    fn minimal_b() {
        assert_snapshot!(p_module(
            r"
module A where

a :: Test
a =
  b
    let
      b =
        let
          f :: forall e. S -> e -> _
          f m e =
            { a: M 1
            , s: Left {}
            }
        in
        do
          m <- g
          E.l M.i
    in [ ]
            "
        ))
    }

    #[test]
    fn minimal_c() {
        assert_snapshot!(p_module(
            r"
module AccessRight where

f x =
  let
    a b =
      case b of
        ABC { a } -> 1
        _ -> 1
  in 1
            "
        ))
    }

    #[test]
    fn minimal_d() {
        assert_snapshot!(p_module(
            r"
module D where

type D = X.Z (A (B.C D)) E
            "
        ))
    }

    #[test]
    fn minimal_e() {
        assert_snapshot!(p_module(
            r"
module E () where

data E
  = E
      { e :: E
      }
  | E E
            "
        ));
    }

    #[test]
    fn minimal_f() {
        assert_snapshot!(p_module(
            r"
module F () where
derive newtype instance Eq Tag
"
        ))
    }

    #[test]
    fn minimal_g() {
        assert_snapshot!(p_module(
            r"
module G () where

g :: G.G (G.G G G) -> G G G
g g =
  g
    <#> G.g (\k v -> G (G k) v)
    # G.gfromFoldable
        "
        ))
    }

    #[test]
    fn minimal_h() {
        assert_snapshot!(p_module(
            r"
module H () where

h = H { tag, attr, children }

h  =HH
        "
        ))
    }

    #[test]
    fn dubble_quals() {
        assert_snapshot!(p_module(
            r"
module H () where

h = A. B. C.
        "
        ))
    }
}
