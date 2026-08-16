//! Pretty-printing (mirror of `Synquid.Pretty`).
//!
//! The `Doc` machinery is a port of the subset of
//! `Text.PrettyPrint.ANSI.Leijen` (ansi-wl-pprint) used by the reference,
//! including the exact `best`/`fits`/`scan` layout algorithm,
//! `renderPretty` (ribbon fraction 0.4, used by `show`/`putDoc`/`hPutDoc`)
//! and ANSI SGR coloring. See the ansi-wl-pprint source for the layout algorithm.

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use crate::{
    error::{ErrorKind, ErrorMessage, Pos},
    logic::{
        ftrue, BinOp, Candidate, Formula, PredSig, QSpace, Sort, SortConstraint, UnOp, DONT_CARE,
        VALUE_VAR_NAME,
    },
    program::{
        all_symbols, unresolved_spec, BareDeclaration, BareProgram, Case, Constraint,
        ConstructorSig, Environment, Goal, MeasureCase, MeasureDef, Program,
    },
    tokens::{bin_op_token_str, un_op_token_str},
    types::{BaseType, RType, SType, SchemaSkeleton, TypeSkeleton, TypeSubstitution},
    util::{as_integer, remove_domain, Id},
};

/// A pretty document (a shared handle to a `DocNode` tree).
pub type Doc = Rc<DocNode>;

/// Indentation amount used by the reference's `tab` constant.
pub const TAB: isize = 2;

/// Abstract pretty document. Mirrors the `Doc` type of ansi-wl-pprint.
#[derive(Clone)]
pub enum DocNode {
    /// Unreachable; produced by flattening a hard `Line`.
    Fail,
    Empty,
    /// A single (non-newline) character.
    Char(char),
    /// A (newline-free) string, with its length.
    Text(usize, String),
    /// Hard line break at the current nesting level.
    Line,
    /// Renders the first argument normally, the second when flattened.
    FlatAlt(Doc, Doc),
    Cat(Doc, Doc),
    Nest(isize, Doc),
    /// Invariant: the first lines of the first argument are longer than
    /// those of the second.
    Union(Doc, Doc),
    Column(Rc<dyn Fn(usize) -> Doc>),
    Nesting(Rc<dyn Fn(usize) -> Doc>),
    /// Introduces coloring around the embedded document.
    Color(ConsoleLayer, ColorIntensity, Color, Doc),
    /// Heavier font weight around the embedded document.
    Intensify(ConsoleIntensity, Doc),
    /// Emitted during rendering to restore the terminal format.
    RestoreFormat(SgrState),
}

/// ANSI color.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Color {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
}

/// Vivid/dull color intensity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColorIntensity {
    Vivid,
    Dull,
}

/// Foreground/background console layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConsoleLayer {
    Foreground,
    Background,
}

/// Font weight.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConsoleIntensity {
    Bold,
    Normal,
}

/// Terminal format state threaded through the renderer.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SgrState {
    pub fc: Option<(ColorIntensity, Color)>,
    pub bc: Option<(ColorIntensity, Color)>,
    pub intensity: Option<ConsoleIntensity>,
}

/// The indentation/document pairs zipper used by the renderers
/// (mirror of `Docs` in ansi-wl-pprint).
type DocStack = Vec<(isize, Doc)>;

impl DocNode {
    fn node(d: DocNode) -> Doc {
        Rc::new(d)
    }
}

/// The empty document: renders as nothing.
#[must_use]
pub fn empty() -> Doc {
    DocNode::node(DocNode::Empty)
}

/// Is document empty?
///
/// Mirrors `isEmpty d = case renderCompact d of SEmpty -> True; _ -> False`.
#[must_use]
pub fn is_empty(d: &Doc) -> bool {
    matches!(render_compact(d), SimpleDoc::SEmpty)
}

/// The document containing the literal string `s` (no newlines).
#[must_use]
pub fn text(s: &str) -> Doc {
    if s.is_empty() {
        empty()
    } else {
        DocNode::node(DocNode::Text(s.len(), s.to_string()))
    }
}

/// The document containing the literal character `c` (not `'\n'`).
#[must_use]
pub fn char_doc(c: char) -> Doc {
    DocNode::node(DocNode::Char(c))
}

/// A hard line break that advances to the next line and indents to the
/// current nesting level (`hardline`).
#[must_use]
pub fn hardline() -> Doc {
    DocNode::node(DocNode::Line)
}

/// A line break that behaves like a space if undone by `group` (`line`).
#[must_use]
pub fn line() -> Doc {
    flat_alt(hardline(), space())
}

/// A line break that behaves like `empty` if undone by `group`
/// (`linebreak`).
#[must_use]
pub fn linebreak() -> Doc {
    flat_alt(hardline(), empty())
}

/// A single space.
#[must_use]
pub fn space() -> Doc {
    char_doc(' ')
}

/// Normally renders the first argument, but when flattened renders the
/// second (`flatAlt`).
#[must_use]
pub fn flat_alt(x: Doc, y: Doc) -> Doc {
    DocNode::node(DocNode::FlatAlt(x, y))
}

/// Concatenation.
#[must_use]
pub fn beside(x: Doc, y: Doc) -> Doc {
    DocNode::node(DocNode::Cat(x, y))
}

/// Increase the indentation level by `i` (`nest`).
#[must_use]
pub fn nest(i: isize, x: Doc) -> Doc {
    DocNode::node(DocNode::Nest(i, x))
}

/// Undo all line breaks in the document; used to specify alternative
/// layouts (`group x = Union (flatten x) x`).
#[must_use]
pub fn group(x: Doc) -> Doc {
    DocNode::node(DocNode::Union(flatten(&x), x))
}

/// Selection between two documents.
fn union(x: Doc, y: Doc) -> Doc {
    DocNode::node(DocNode::Union(x, y))
}

/// Flatten a document.
#[must_use]
pub fn flatten(d: &Doc) -> Doc {
    match &**d {
        DocNode::Fail => d.clone(),
        DocNode::Empty => d.clone(),
        DocNode::Char(_) => d.clone(),
        DocNode::Text(..) => d.clone(),
        DocNode::Line => DocNode::node(DocNode::Fail),
        DocNode::FlatAlt(_, y) => y.clone(),
        DocNode::Cat(x, y) => beside(flatten(x), flatten(y)),
        DocNode::Nest(i, x) => nest(*i, flatten(x)),
        DocNode::Union(x, _) => flatten(x),
        DocNode::Column(f) => {
            let f = f.clone();
            column(Box::new(move |k| flatten(&f(k))))
        }
        DocNode::Nesting(f) => {
            let f = f.clone();
            nesting(Box::new(move |i| flatten(&f(i))))
        }
        DocNode::Color(l, i, c, x) => color(*l, *i, *c, flatten(x)),
        DocNode::Intensify(i, x) => intensify(*i, flatten(x)),
        DocNode::RestoreFormat(s) => DocNode::node(DocNode::RestoreFormat(*s)),
    }
}

/// A document whose rendering depends on the current column.
#[must_use]
pub fn column(f: Box<dyn Fn(usize) -> Doc>) -> Doc {
    DocNode::node(DocNode::Column(Rc::from(f)))
}

/// A document whose rendering depends on the current nesting level.
#[must_use]
pub fn nesting(f: Box<dyn Fn(usize) -> Doc>) -> Doc {
    DocNode::node(DocNode::Nesting(Rc::from(f)))
}

/// A document that renders `d` with the nesting level set to the current
/// column (`align d = column (\k -> nesting (\i -> nest (k - i) d))`).
#[must_use]
pub fn align(d: Doc) -> Doc {
    column(Box::new(move |k| {
        let d = d.clone();
        nesting(Box::new(move |i| {
            nest(usize_to_isize(k) - usize_to_isize(i), d.clone())
        }))
    }))
}

/// Hanging indentation: render `d` with the nesting level set to the
/// current column plus `i` (`hang i d = align (nest i d)`).
#[must_use]
pub fn hang(i: isize, d: Doc) -> Doc {
    align(nest(i, d))
}

/// Indent `d` with `i` spaces (`indent i d = hang i (text (spaces i) <> d)`).
#[must_use]
pub fn indent(i: isize, d: Doc) -> Doc {
    hang(i, beside(text(&spaces_str(isize_to_usize(i))), d))
}

/// A document that measures the width of `d` and passes it to `f`
/// (`width d f = column (\k1 -> d <> column (\k2 -> f (k2 - k1)))`).
#[must_use]
pub fn width(d: Doc, f: Box<dyn Fn(usize) -> Doc>) -> Doc {
    let f: Rc<dyn Fn(usize) -> Doc> = Rc::from(f);
    column(Box::new(move |k1| {
        let d = d.clone();
        let f = f.clone();
        beside(d, column(Box::new(move |k2| f(k2 - k1))))
    }))
}

/// Append spaces until the width is equal to `f`, or break if already
/// larger (`fillBreak`).
#[must_use]
pub fn fill_break(f: usize, x: Doc) -> Doc {
    width(
        x,
        Box::new(move |w| {
            if w > f {
                nest(usize_to_isize(f), linebreak())
            } else {
                text(&spaces_str(f - w))
            }
        }),
    )
}

/// Append spaces until the width is equal to `f` (`fill`).
#[must_use]
pub fn fill(f: usize, d: Doc) -> Doc {
    width(
        d,
        Box::new(move |w| {
            if w >= f {
                empty()
            } else {
                text(&spaces_str(f - w))
            }
        }),
    )
}

/// Right-align a simple document: pad with spaces to width `w` (`lfill`; only works for documents that compact to a single `SText`).
#[must_use]
pub fn lfill(w: usize, d: Doc) -> Doc {
    match render_compact(&d) {
        SimpleDoc::SText(len, ..) => {
            let pad = spaces_str(w.saturating_sub(len));
            beside(text(&pad), d)
        }
        _ => panic!("lfill: document does not compact to a single string"),
    }
}

/// A document that displays `s`, replacing newlines with `line` (`string`).
#[must_use]
pub fn string_doc(s: &str) -> Doc {
    let mut parts = Vec::new();
    for chunk in s.split('\n') {
        if !parts.is_empty() {
            parts.push(line());
        }
        parts.push(text(chunk));
    }
    hcat(parts)
}

/// A document containing a string of `n` spaces.
#[must_use]
pub fn spaces_str(n: usize) -> String {
    " ".repeat(n)
}

/// Enclose `x` between `l` and `r`.
#[must_use]
pub fn enclose(l: Doc, r: Doc, x: Doc) -> Doc {
    beside(l, beside(x, r))
}

/// Comma-separated list of documents, enclosed in square brackets.
#[must_use]
pub fn list(ds: Vec<Doc>) -> Doc {
    enclose_sep(&lbracket(), &rbracket(), &comma(), ds)
}

/// Comma-separated list of documents, enclosed in parentheses.
#[must_use]
pub fn tupled(ds: Vec<Doc>) -> Doc {
    enclose_sep(&lparen(), &rparen(), &comma(), ds)
}

/// Enclose `ds` with `l` and `r`, separated by `sep`. Renders horizontally
/// if it fits the page, otherwise aligned vertically with separators in
/// front (`encloseSep`).
#[must_use]
pub fn enclose_sep(left: &Doc, right: &Doc, sep: &Doc, ds: Vec<Doc>) -> Doc {
    match ds.as_slice() {
        [] => beside(left.clone(), right.clone()),
        [d] => beside(left.clone(), beside(d.clone(), right.clone())),
        _ => {
            let mut doc_list = Vec::with_capacity(ds.len());
            let mut it = ds.into_iter();
            if let Some(first) = it.next() {
                doc_list.push(beside(left.clone(), first));
            }
            for d in it {
                doc_list.push(beside(sep.clone(), d));
            }
            align(beside(cat(doc_list), right.clone()))
        }
    }
}

/// Concatenate all documents in `ds` with `p` except the last (`punctuate`).
#[must_use]
pub fn punctuate(p: &Doc, ds: Vec<Doc>) -> Vec<Doc> {
    let n = ds.len();
    let mut res = Vec::with_capacity(n);
    for (i, d) in ds.into_iter().enumerate() {
        res.push(if i + 1 == n { d } else { beside(d, p.clone()) });
    }
    res
}

fn foldr1(f: impl Fn(Doc, Doc) -> Doc, ds: Vec<Doc>) -> Doc {
    let mut it = ds.into_iter().rev();
    let Some(mut acc) = it.next() else {
        return empty();
    };
    for d in it {
        acc = f(d, acc);
    }
    acc
}

/// Concatenate all documents horizontally (`hcat`).
pub fn hcat(ds: Vec<Doc>) -> Doc {
    foldr1(beside, ds)
}

/// Concatenate all documents vertically, directly (`vcat`, using
/// `linebreak`).
#[must_use]
pub fn vcat(ds: Vec<Doc>) -> Doc {
    foldr1(|x, y| beside(x, beside(linebreak(), y)), ds)
}

/// Grouped vertical concatenation (`cat = group . vcat`).
#[must_use]
pub fn cat(ds: Vec<Doc>) -> Doc {
    group(vcat(ds))
}

/// Concatenate documents horizontally with spaces, if they fit; otherwise
/// aligned vertically (`sep = group . vsep`).
#[must_use]
pub fn sep(ds: Vec<Doc>) -> Doc {
    group(vsep(ds))
}

/// Concatenate documents horizontally, with spaces (`hsep`: empty documents are skipped).
pub fn hsep(ds: Vec<Doc>) -> Doc {
    foldr1(hsp, ds)
}

/// Concatenate documents vertically, with newlines (`vsep`: empty documents are skipped).
pub fn vsep(ds: Vec<Doc>) -> Doc {
    foldr1(vsp, ds)
}

/// Separator characters.
#[must_use]
pub fn lparen() -> Doc {
    char_doc('(')
}
#[must_use]
pub fn rparen() -> Doc {
    char_doc(')')
}
#[must_use]
pub fn langle() -> Doc {
    char_doc('<')
}
#[must_use]
pub fn rangle() -> Doc {
    char_doc('>')
}
#[must_use]
pub fn lbrace() -> Doc {
    char_doc('{')
}
#[must_use]
pub fn rbrace() -> Doc {
    char_doc('}')
}
#[must_use]
pub fn lbracket() -> Doc {
    char_doc('[')
}
#[must_use]
pub fn rbracket() -> Doc {
    char_doc(']')
}
#[must_use]
pub fn squote() -> Doc {
    char_doc('\'')
}
#[must_use]
pub fn dquote() -> Doc {
    char_doc('"')
}
#[must_use]
pub fn semi() -> Doc {
    char_doc(';')
}
#[must_use]
pub fn colon() -> Doc {
    char_doc(':')
}
#[must_use]
pub fn comma() -> Doc {
    char_doc(',')
}
#[must_use]
pub fn dot() -> Doc {
    char_doc('.')
}
#[must_use]
pub fn backslash() -> Doc {
    char_doc('\\')
}
#[must_use]
pub fn equals() -> Doc {
    char_doc('=')
}

/// Enclosing combinators.
#[must_use]
pub fn squotes(d: Doc) -> Doc {
    enclose(squote(), squote(), d)
}
#[must_use]
pub fn dquotes(d: Doc) -> Doc {
    enclose(dquote(), dquote(), d)
}
#[must_use]
pub fn braces(d: Doc) -> Doc {
    enclose(lbrace(), rbrace(), d)
}
#[must_use]
pub fn parens(d: Doc) -> Doc {
    enclose(lparen(), rparen(), d)
}
#[must_use]
pub fn angles(d: Doc) -> Doc {
    enclose(langle(), rangle(), d)
}
#[must_use]
pub fn brackets(d: Doc) -> Doc {
    enclose(lbracket(), rbracket(), d)
}

/// Concatenate `x` and `y` with a space in between (`x <> space <> y`).
fn sp(x: Doc, y: Doc) -> Doc {
    beside(x, beside(space(), y))
}

/// Concatenate `x` and `y` with a line in between (`x <> line <> y`).
fn line_sp(x: Doc, y: Doc) -> Doc {
    beside(x, beside(line(), y))
}

/// Concatenate `x` and `y` with a softline in between (`x <> softline <> y`).
fn softline_sp(x: Doc, y: Doc) -> Doc {
    beside(x, beside(softline(), y))
}

/// Separates two documents by a space if both are nonempty (`<+>`).
#[must_use]
pub fn hsp(x: Doc, y: Doc) -> Doc {
    if is_empty(&x) {
        y
    } else if is_empty(&y) {
        x
    } else {
        sp(x, y)
    }
}

/// Separates two documents by a line if both are nonempty (`$+$`).
#[must_use]
pub fn vsp(x: Doc, y: Doc) -> Doc {
    if is_empty(&x) {
        y
    } else if is_empty(&y) {
        x
    } else {
        line_sp(x, y)
    }
}

/// Concatenate `x` and `y` with a linebreak in between (`</>`).
#[must_use]
pub fn soft_break(x: Doc, y: Doc) -> Doc {
    softline_sp(x, y)
}

/// Separates documents by commas (`commaSep = hsep . punctuate comma`).
#[must_use]
pub fn comma_sep(ds: Vec<Doc>) -> Doc {
    hsep(punctuate(&comma(), ds))
}

/// Enclose a document in spaces (`spaces d = space <> d <> space`).
#[must_use]
pub fn spaces_doc(d: Doc) -> Doc {
    beside(space(), beside(d, space()))
}

/// Conditionally enclose in parentheses (`condParens`).
#[must_use]
pub fn cond_parens(b: bool, d: Doc) -> Doc {
    if b {
        parens(d)
    } else {
        d
    }
}

/// Conditionally produce a document (`option`).
#[must_use]
pub fn option(b: bool, d: Doc) -> Doc {
    if b {
        d
    } else {
        empty()
    }
}

/// Convert an `Option` value to a document (`optionMaybe`).
pub fn option_maybe<T>(m: Option<T>, to_doc: impl FnOnce(T) -> Doc) -> Doc {
    match m {
        None => empty(),
        Some(v) => to_doc(v),
    }
}

/// A soft line break: a space if the result fits, a line otherwise
/// (`softline = group line`).
#[must_use]
pub fn softline() -> Doc {
    group(line())
}

/// A soft break: empty if it fits, a line otherwise
/// (`softbreak = group linebreak`).
#[must_use]
pub fn softbreak() -> Doc {
    group(linebreak())
}

/// Display `d` with a vivid forecolor (`color`).
#[must_use]
pub fn color(layer: ConsoleLayer, intensity: ColorIntensity, c: Color, d: Doc) -> Doc {
    DocNode::node(DocNode::Color(layer, intensity, c, d))
}

/// Display `d` with a heavier font weight (`bold`).
#[must_use]
pub fn intensify(i: ConsoleIntensity, d: Doc) -> Doc {
    DocNode::node(DocNode::Intensify(i, d))
}

/// Remove all colorisation and emboldening from a document (`plain`).
#[must_use]
pub fn plain(d: &Doc) -> Doc {
    match &**d {
        DocNode::Fail => d.clone(),
        DocNode::Empty => d.clone(),
        DocNode::Char(_) => d.clone(),
        DocNode::Text(..) => d.clone(),
        DocNode::Line => d.clone(),
        DocNode::FlatAlt(x, y) => flat_alt(plain(x), plain(y)),
        DocNode::Cat(x, y) => beside(plain(x), plain(y)),
        DocNode::Nest(i, x) => nest(*i, plain(x)),
        DocNode::Union(x, y) => union(plain(x), plain(y)),
        DocNode::Column(f) => {
            let f = f.clone();
            column(Box::new(move |k| plain(&f(k))))
        }
        DocNode::Nesting(f) => {
            let f = f.clone();
            nesting(Box::new(move |i| plain(&f(i))))
        }
        DocNode::Color(_, _, _, x) => plain(x),
        DocNode::Intensify(_, x) => plain(x),
        DocNode::RestoreFormat(_) => empty(),
    }
}

fn color_code(layer: ConsoleLayer, intensity: ColorIntensity, c: Color) -> String {
    let base = match (layer, intensity) {
        (ConsoleLayer::Foreground, ColorIntensity::Vivid) => 90,
        (ConsoleLayer::Foreground, ColorIntensity::Dull) => 30,
        (ConsoleLayer::Background, ColorIntensity::Vivid) => 100,
        (ConsoleLayer::Background, ColorIntensity::Dull) => 40,
    };
    let idx = match c {
        Color::Black => 0,
        Color::Red => 1,
        Color::Green => 2,
        Color::Yellow => 3,
        Color::Blue => 4,
        Color::Magenta => 5,
        Color::Cyan => 6,
        Color::White => 7,
    };
    format!("\u{1b}[{}m", base + idx)
}

fn console_intensity_code(i: ConsoleIntensity) -> String {
    match i {
        ConsoleIntensity::Bold => "1".to_string(),
        ConsoleIntensity::Normal => "22".to_string(),
    }
}

/// SGR escape code restoring a format state (`Reset : catMaybes ...` in the
/// reference's `RestoreFormat` case).
fn restore_code(st: SgrState) -> String {
    let mut codes = vec!["0".to_string()];
    if let Some((i, c)) = st.fc {
        codes.push(sgr_code(ConsoleLayer::Foreground, i, c));
    }
    if let Some((i, c)) = st.bc {
        codes.push(sgr_code(ConsoleLayer::Background, i, c));
    }
    if let Some(i) = st.intensity {
        codes.push(console_intensity_code(i));
    }
    format!("\u{1b}[{}m", codes.join(";"))
}

fn sgr_code(layer: ConsoleLayer, intensity: ColorIntensity, c: Color) -> String {
    format!(
        "{}{}",
        match layer {
            ConsoleLayer::Foreground => match intensity {
                ColorIntensity::Vivid => "9",
                ColorIntensity::Dull => "3",
            },
            ConsoleLayer::Background => match intensity {
                ColorIntensity::Vivid => "10",
                ColorIntensity::Dull => "4",
            },
        },
        match c {
            Color::Black => "0",
            Color::Red => "1",
            Color::Green => "2",
            Color::Yellow => "3",
            Color::Blue => "4",
            Color::Magenta => "5",
            Color::Cyan => "6",
            Color::White => "7",
        }
    )
}

/// Rendered documents (mirror of `SimpleDoc`).
#[derive(Clone, Debug, PartialEq)]
pub enum SimpleDoc {
    SFail,
    SEmpty,
    SChar(char, Box<SimpleDoc>),
    SText(usize, String, Box<SimpleDoc>),
    SLine(usize, Box<SimpleDoc>),
    SSgr(String, Box<SimpleDoc>),
}

/// Output items produced while rendering.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum OutTok {
    Char(char),
    Text(String),
    Line(usize),
    Sgr(String),
}

/// The default pretty printer (`renderPretty`), mirroring the `best`
/// algorithm of ansi-wl-pprint: `best 0 0 ... (Cons 0 x Nil)`, with
/// ribbon width `r = max 0 (min w (round (w * rfrac)))`.
#[must_use]
#[allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    reason = "ribbon computation mirrors the reference's lossless `Int`/`Rational` conversions; rfrac is always 0.4"
)]
pub fn render_pretty(rfrac: f64, width: usize, d: &Doc) -> SimpleDoc {
    let r = isize::max(
        0,
        isize::min(width as isize, (width as f64 * rfrac).round() as isize),
    );
    let out = best(
        width as isize,
        r,
        0,
        0,
        SgrState::default(),
        vec![(0, d.clone())],
    );
    simple_doc_of(out)
}

/// Convert the rendered output items into a `SimpleDoc` chain.
fn simple_doc_of(items: Vec<OutTok>) -> SimpleDoc {
    let mut rest = SimpleDoc::SEmpty;
    for tok in items.into_iter().rev() {
        rest = match tok {
            OutTok::Char(c) => SimpleDoc::SChar(c, Box::new(rest)),
            OutTok::Text(s) => {
                let l = s.len();
                SimpleDoc::SText(l, s, Box::new(rest))
            }
            OutTok::Line(i) => SimpleDoc::SLine(i, Box::new(rest)),
            OutTok::Sgr(s) => SimpleDoc::SSgr(s, Box::new(rest)),
        };
    }
    rest
}

/// Lossless-ish `usize` -> `isize` conversion used by the renderer, where the
/// values mirror the reference's `Int` arithmetic (never near the boundary).
#[must_use]
fn usize_to_isize(x: usize) -> isize {
    isize::try_from(x).unwrap_or(isize::MAX)
}

/// Lossless-ish `isize` -> `usize` conversion (clamps negatives to `0`,
/// matching the reference's `max 0` guards before `Int` -> `Int` casts).
#[must_use]
fn isize_to_usize(x: isize) -> usize {
    usize::try_from(x).unwrap_or(0)
}

/// The core layout algorithm (`best`), written iteratively with an explicit
/// zipper stack, mirroring the reference `best`/`nicest`/`fits1`.
fn best(
    w: isize,
    r: isize,
    mut n: isize,
    mut k: isize,
    mut state: SgrState,
    mut stack: DocStack,
) -> Vec<OutTok> {
    let mut out = Vec::new();
    loop {
        let Some((i, d)) = stack.pop() else {
            break;
        };
        match &*d {
            DocNode::Fail => {
                panic!("best: SFail can not appear uncaught in a rendered SimpleDoc")
            }
            DocNode::Empty => {}
            DocNode::Char(c) => {
                out.push(OutTok::Char(*c));
                k += 1;
            }
            DocNode::Text(l, s) => {
                out.push(OutTok::Text(s.clone()));
                k += usize_to_isize(*l);
            }
            DocNode::Line => {
                out.push(OutTok::Line(i.max(0) as usize));
                n = i;
                k = i;
            }
            DocNode::FlatAlt(x, _) => stack.push((i, x.clone())),
            DocNode::Cat(x, y) => {
                stack.push((i, y.clone()));
                stack.push((i, x.clone()));
            }
            DocNode::Nest(j, x) => stack.push((i + j, x.clone())),
            DocNode::Union(x, y) => {
                let width = isize::min(w - k, r - k + n);
                let mut sub = stack.clone();
                sub.push((i, x.clone()));
                if fits(w, r, width, n, k, &mut sub) {
                    stack.push((i, x.clone()));
                } else {
                    stack.push((i, y.clone()));
                }
            }
            DocNode::Column(f) => stack.push((i, f(isize_to_usize(k)))),
            DocNode::Nesting(f) => stack.push((i, f(isize_to_usize(i)))),
            DocNode::Color(l, ci, c, x) => {
                out.push(OutTok::Sgr(color_code(*l, *ci, *c)));
                let old = state;
                state = match l {
                    ConsoleLayer::Foreground => SgrState {
                        fc: Some((*ci, *c)),
                        ..state
                    },
                    ConsoleLayer::Background => SgrState {
                        bc: Some((*ci, *c)),
                        ..state
                    },
                };
                stack.push((i, DocNode::node(DocNode::RestoreFormat(old))));
                stack.push((i, x.clone()));
            }
            DocNode::Intensify(ci, x) => {
                out.push(OutTok::Sgr(format!(
                    "\u{1b}[{}m",
                    console_intensity_code(*ci)
                )));
                let old = state;
                state = SgrState {
                    intensity: Some(*ci),
                    ..state
                };
                stack.push((i, DocNode::node(DocNode::RestoreFormat(old))));
                stack.push((i, x.clone()));
            }
            DocNode::RestoreFormat(restore) => {
                out.push(OutTok::Sgr(restore_code(*restore)));
                state = *restore;
            }
        }
    }
    out
}

/// The one-line lookahead fit test (`fits1` in the reference), walking the
/// rendered first line of a pending zipper. `w0` is the page width and `r`
/// the ribbon width; the remainder of the arguments mirror `best`'s state.
fn fits(w0: isize, r: isize, mut w: isize, n: isize, mut k: isize, stack: &mut DocStack) -> bool {
    loop {
        if w < 0 {
            return false;
        }
        let Some((i, d)) = stack.pop() else {
            return true;
        };
        match &*d {
            DocNode::Fail => return false,
            DocNode::Empty => {}
            DocNode::Char(_) => {
                w -= 1;
                k += 1;
            }
            DocNode::Text(l, _) => {
                w -= usize_to_isize(*l);
                k += usize_to_isize(*l);
            }
            DocNode::Line => return true,
            DocNode::FlatAlt(x, _) => stack.push((i, x.clone())),
            DocNode::Cat(x, y) => {
                stack.push((i, y.clone()));
                stack.push((i, x.clone()));
            }
            DocNode::Nest(j, x) => stack.push((i + j, x.clone())),
            DocNode::Union(x, y) => {
                let width = isize::min(w0 - k, r - k + n);
                let mut sub = stack.clone();
                sub.push((i, x.clone()));
                if fits(w0, r, width, n, k, &mut sub) {
                    stack.push((i, x.clone()));
                } else {
                    stack.push((i, y.clone()));
                }
            }
            DocNode::Column(f) => stack.push((i, f(isize_to_usize(k)))),
            DocNode::Nesting(f) => stack.push((i, f(isize_to_usize(i)))),
            DocNode::Color(_, _, _, x) | DocNode::Intensify(_, x) => {
                // The reference's `fits1` walks into the SGR-wrapped content
                // (`fits1 p m w (SSGR _ x) = fits1 p m w x`): the escape
                // codes are free, but the wrapped document still counts
                // toward the width and its internal line breaks still stop
                // the lookahead.
                stack.push((i, x.clone()));
            }
            DocNode::RestoreFormat(..) => {}
        }
    }
}

/// Renders a document without adding any indentation or newlines
/// (`renderCompact`); used by `isEmpty` and `lfill`.
#[must_use]
pub fn render_compact(d: &Doc) -> SimpleDoc {
    fn scan(k: usize, stack: &mut Vec<Doc>) -> SimpleDoc {
        loop {
            let Some(d) = stack.pop() else {
                return SimpleDoc::SEmpty;
            };
            match &*d {
                DocNode::Fail => return SimpleDoc::SFail,
                DocNode::Empty => {}
                DocNode::Char(c) => {
                    return SimpleDoc::SChar(*c, Box::new(scan(k + 1, stack)));
                }
                DocNode::Text(l, s) => {
                    return SimpleDoc::SText(*l, s.clone(), Box::new(scan(k + l, stack)));
                }
                DocNode::Line => {
                    return SimpleDoc::SLine(0, Box::new(scan(0, stack)));
                }
                DocNode::FlatAlt(x, _) => stack.push(x.clone()),
                DocNode::Cat(x, y) => {
                    stack.push(y.clone());
                    stack.push(x.clone());
                }
                DocNode::Nest(_, x) => stack.push(x.clone()),
                DocNode::Union(_, y) => stack.push(y.clone()),
                DocNode::Column(f) => stack.push(f(k)),
                DocNode::Nesting(f) => stack.push(f(0)),
                DocNode::Color(..) | DocNode::Intensify(..) => {
                    if let DocNode::Color(_, _, _, x) = &*d {
                        stack.push(x.clone());
                    } else if let DocNode::Intensify(_, x) = &*d {
                        stack.push(x.clone());
                    }
                }
                DocNode::RestoreFormat(_) => {}
            }
        }
    }
    scan(0, &mut vec![d.clone()])
}

/// Turn a `SimpleDoc` into a string (`displayS`), with SGR escape codes for
/// coloring and `\n` + indentation for line breaks.
#[must_use]
pub fn display(doc: &SimpleDoc) -> String {
    fn go(doc: &SimpleDoc, acc: &mut String) {
        match doc {
            SimpleDoc::SFail => {
                panic!("display: SFail can not appear uncaught in a rendered SimpleDoc")
            }
            SimpleDoc::SEmpty => {}
            SimpleDoc::SChar(c, rest) => {
                acc.push(*c);
                go(rest, acc);
            }
            SimpleDoc::SText(_, s, rest) => {
                acc.push_str(s);
                go(rest, acc);
            }
            SimpleDoc::SLine(i, rest) => {
                acc.push('\n');
                acc.push_str(&spaces_str(*i));
                go(rest, acc);
            }
            SimpleDoc::SSgr(s, rest) => {
                acc.push_str(s);
                go(rest, acc);
            }
        }
    }
    let mut acc = String::new();
    go(doc, &mut acc);
    acc
}

/// Pretty-print `d` to a string with the default page width of 80 and
/// ribbon width of 0.4 * 80 (the reference's `instance Show Doc` and
/// `putDoc`).
#[must_use]
pub fn show_doc(d: &Doc) -> String {
    display(&render_pretty(0.4, 80, d))
}

/// The pretty-printing class (mirror of `class Pretty a`).
pub trait Pretty {
    fn pretty(&self) -> Doc;
}

impl Pretty for Doc {
    fn pretty(&self) -> Doc {
        self.clone()
    }
}

impl Pretty for String {
    fn pretty(&self) -> Doc {
        string_doc(self)
    }
}

impl Pretty for bool {
    fn pretty(&self) -> Doc {
        if *self {
            text("True")
        } else {
            text("False")
        }
    }
}

impl Pretty for i64 {
    fn pretty(&self) -> Doc {
        text(&self.to_string())
    }
}

impl Pretty for usize {
    fn pretty(&self) -> Doc {
        text(&self.to_string())
    }
}

impl Pretty for () {
    fn pretty(&self) -> Doc {
        text("()")
    }
}

/// Binding power of a formula (`power`).
#[must_use]
pub const fn power(fml: &Formula) -> usize {
    match fml {
        Formula::Pred(_, _, args) | Formula::Cons(_, _, args) if args.is_empty() => 10,
        Formula::Pred(..) | Formula::Cons(..) => 9,
        Formula::Unary(..) => 8,
        Formula::Binary(op, ..) => match op {
            BinOp::Times | BinOp::Intersect => 7,
            BinOp::Plus | BinOp::Minus | BinOp::Union | BinOp::Diff => 6,
            BinOp::Eq
            | BinOp::Neq
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Member
            | BinOp::Subset => 5,
            BinOp::And | BinOp::Or => 4,
            BinOp::Implies => 3,
            BinOp::Iff => 2,
        },
        Formula::All(..) | Formula::Ite(..) => 1,
        _ => 10,
    }
}

/// Pretty-printed formula (`fmlDoc = fmlDocAt 0`).
#[must_use]
pub fn fml_doc(fml: &Formula) -> Doc {
    fml_doc_at(0, fml)
}

/// Pretty-printed formula in a context of binding power `n` (`fmlDocAt`).
pub fn fml_doc_at(n: usize, fml: &Formula) -> Doc {
    let n_ctx = power(fml);
    let body = match fml {
        Formula::BoolLit(b) => b.pretty(),
        Formula::IntLit(i) => int_literal(*i),
        Formula::SetLit(_, elems) => hl_brackets(comma_sep(elems.iter().map(fml_doc).collect())),
        Formula::Var(_, name) => {
            if name == VALUE_VAR_NAME {
                special(name)
            } else {
                text(name)
            }
        }
        Formula::Unknown(s, name) => {
            if s.is_empty() {
                text(name)
            } else {
                beside(h_map_doc(s), text(name))
            }
        }
        Formula::Unary(op, e) => {
            let op_doc = maybe_operator(&un_op_token_str(*op));
            beside(op_doc, fml_doc_at(n_ctx, e))
        }
        Formula::Binary(op, e1, e2) => {
            let op_doc = maybe_operator(&bin_op_token_str(*op));
            hsp(fml_doc_at(n_ctx, e1), hsp(op_doc, fml_doc_at(n_ctx, e2)))
        }
        Formula::Ite(e0, e1, e2) => {
            let kw = |s: &str| keyword(s);
            hsp(
                kw("if"),
                hsp(
                    fml_doc(e0),
                    hsp(kw("then"), hsp(fml_doc(e1), hsp(kw("else"), fml_doc(e2)))),
                ),
            )
        }
        Formula::Pred(_, name, args) => hsp(
            text(name),
            hsep(args.iter().map(|a| fml_doc_at(n_ctx, a)).collect()),
        ),
        Formula::Cons(_, name, args) => hl_parens(hsp(
            text(name),
            hsep(args.iter().map(|a| fml_doc_at(n_ctx, a)).collect()),
        )),
        Formula::All(x, e) => {
            let kw = |s: &str| keyword(s);
            hsp(
                kw("forall"),
                hsp(x.pretty(), hsp(maybe_operator("."), fml_doc(e))),
            )
        }
    };
    cond_hl_parens(n_ctx <= n, body)
}

impl Pretty for Formula {
    fn pretty(&self) -> Doc {
        fml_doc(self)
    }
}

impl Pretty for BTreeSet<Formula> {
    fn pretty(&self) -> Doc {
        braces(comma_sep(self.iter().map(|f| f.pretty()).collect()))
    }
}

impl Pretty for BTreeMap<Id, BTreeSet<Formula>> {
    fn pretty(&self) -> Doc {
        h_map_doc(self)
    }
}

impl Pretty for QSpace {
    fn pretty(&self) -> Doc {
        braces(comma_sep(
            self.qualifiers.iter().map(|f| f.pretty()).collect(),
        ))
    }
}

impl Pretty for BTreeMap<Id, QSpace> {
    fn pretty(&self) -> Doc {
        v_map_doc(self)
    }
}

impl Pretty for Sort {
    fn pretty(&self) -> Doc {
        match self {
            Sort::IntS => text("Int"),
            Sort::BoolS => text("Bool"),
            Sort::SetS(el) => hsp(text("Set"), el.pretty()),
            Sort::VarS(name) => text(name),
            Sort::DataS(name, args) => {
                let arg_docs = args.iter().map(|a| hl_parens(a.pretty())).collect();
                hsp(text(name), hsep(arg_docs))
            }
            Sort::AnyS => maybe_operator("?"),
        }
    }
}

impl Pretty for PredSig {
    fn pretty(&self) -> Doc {
        let arrows: Vec<Doc> = self
            .pred_sig_arg_sorts
            .iter()
            .map(|s| hsp(s.pretty(), text("->")))
            .collect();
        let body = hsp(
            hsp(text(&self.pred_sig_name), text("::")),
            hsp(hsep(arrows), self.pred_sig_res_sort.pretty()),
        );
        hl_angles(body)
    }
}

impl Pretty for UnOp {
    fn pretty(&self) -> Doc {
        maybe_operator(&un_op_token_str(*self))
    }
}

impl Pretty for BinOp {
    fn pretty(&self) -> Doc {
        maybe_operator(&bin_op_token_str(*self))
    }
}

/// Pretty-printed refinement type (`prettyType = prettyTypeAt 0`).
#[must_use]
pub fn pretty_type(t: &RType) -> Doc {
    pretty_type_at(0, t)
}

/// Binding power of a type (`typePower`).
#[must_use]
pub fn type_power(t: &RType) -> usize {
    match t {
        TypeSkeleton::FunctionT(..) => 1,
        TypeSkeleton::ScalarT(BaseType::DatatypeT(_, t_args, p_args), r)
            if (!t_args.is_empty() || !p_args.is_empty()) && *r == ftrue() =>
        {
            2
        }
        _ => 3,
    }
}

/// Pretty-printed type in a context of binding power `n` (`prettyTypeAt`).
pub fn pretty_type_at(n: usize, t: &RType) -> Doc {
    let n_ctx = type_power(t);
    let body = match t {
        TypeSkeleton::ScalarT(base, fml) => match fml {
            Formula::BoolLit(true) => pretty_base::<Formula>(t_arg_pretty_ctx, base),
            fml => {
                let inner = beside(
                    pretty_base::<Formula>(t_arg_pretty_ctx, base),
                    maybe_operator("|"),
                );
                hl_braces(beside(inner, fml.pretty()))
            }
        },
        TypeSkeleton::AnyT => text("_"),
        TypeSkeleton::FunctionT(x, t1, t2) => {
            // `text x <> operator ":" <+> prettyTypeAt n' t1 <+> operator "->" <+>
            // prettyTypeAt 0 t2` in the reference: the binder and its colon are
            // glued to the argument type (the rendered output has `x:t1`, not
            // `x: t1`).
            let binds = beside(
                beside(text(x), maybe_operator(":")),
                pretty_type_at(n_ctx, t1),
            );
            hsp(binds, hsp(maybe_operator("->"), pretty_type_at(0, t2)))
        }
        TypeSkeleton::LetT(x, t1, t2) => {
            let binds = beside(
                beside(text(x), maybe_operator(":")),
                pretty_type_at(n_ctx, t1),
            );
            hsp(
                text("LET"),
                hsp(binds, hsp(text("IN"), pretty_type_at(0, t2))),
            )
        }
    };
    cond_hl_parens(n_ctx <= n, body)
}

/// Type-argument pretty printer used for `BaseType<Formula>` type arguments
/// (`prettyTypeAt 1`).
fn t_arg_pretty_ctx(a: &TypeSkeleton<Formula>) -> Doc {
    pretty_type_at(1, a)
}

/// Pretty-printed base type (`prettyBase`).
pub fn pretty_base<R: Pretty>(
    pretty_type: impl Fn(&TypeSkeleton<R>) -> Doc,
    base: &BaseType<R>,
) -> Doc {
    match base {
        BaseType::IntT => text("Int"),
        BaseType::BoolT => text("Bool"),
        BaseType::TypeVarT(s, name) => {
            if s.is_empty() {
                text(name)
            } else {
                beside(h_map_doc(s), text(name))
            }
        }
        BaseType::DatatypeT(name, t_args, p_args) => {
            let args: Vec<Doc> = t_args.iter().map(pretty_type).collect();
            let p_args: Vec<Doc> = p_args.iter().map(|a| hl_angles(a.pretty())).collect();
            hsp(hsp(text(name), hsep(args)), hsep(p_args))
        }
    }
}

impl Pretty for BaseType<()> {
    fn pretty(&self) -> Doc {
        pretty_base(|a| hl_parens(a.pretty()), self)
    }
}

impl Pretty for BaseType<Formula> {
    fn pretty(&self) -> Doc {
        pretty_base(t_arg_pretty_ctx, self)
    }
}

/// Pretty-printed unrefined type (`prettySType`).
#[must_use]
pub fn pretty_s_type(t: &SType) -> Doc {
    match t {
        TypeSkeleton::ScalarT(base, ()) => base.pretty(),
        TypeSkeleton::FunctionT(_, t1, t2) => {
            hl_parens(hsp(hsp(t1.pretty(), maybe_operator("->")), t2.pretty()))
        }
        TypeSkeleton::AnyT => text("_"),
        TypeSkeleton::LetT(..) => panic!("prettySType: contextual type"),
    }
}

impl Pretty for TypeSkeleton<()> {
    fn pretty(&self) -> Doc {
        pretty_s_type(self)
    }
}

impl Pretty for TypeSkeleton<Formula> {
    fn pretty(&self) -> Doc {
        pretty_type(self)
    }
}

/// Pretty-printed schema (`prettySchema`).
pub fn pretty_schema<R>(sch: &SchemaSkeleton<R>) -> Doc
where
    TypeSkeleton<R>: Pretty,
{
    match sch {
        SchemaSkeleton::Monotype(t) => t.pretty(),
        SchemaSkeleton::ForallT(a, sch) => hsp(
            hl_angles(text(a)),
            hsp(maybe_operator("."), pretty_schema(sch)),
        ),
        SchemaSkeleton::ForallP(sig, sch) => {
            hsp(sig.pretty(), hsp(maybe_operator("."), pretty_schema(sch)))
        }
    }
}

impl Pretty for SchemaSkeleton<()> {
    fn pretty(&self) -> Doc {
        pretty_schema(self)
    }
}

impl Pretty for SchemaSkeleton<Formula> {
    fn pretty(&self) -> Doc {
        pretty_schema(self)
    }
}

impl Pretty for TypeSubstitution {
    fn pretty(&self) -> Doc {
        h_map_doc(self)
    }
}

/// Pretty-printed case of a pattern match (`prettyCase`).
pub fn pretty_case<T: Pretty>(cas: &Case<T>) -> Doc {
    let args: Vec<Doc> = cas.arg_names.iter().map(|a| text(a)).collect();
    let head = hsp(
        hsp(text(&cas.constructor), hsep(args)),
        maybe_operator("->"),
    );
    hang(TAB, soft_break(head, pretty_program_f(&cas.expr)))
}

/// Pretty-printed program (`prettyProgram`).
pub fn pretty_program<T: Pretty>(p: &Program<T>) -> Doc {
    pretty_program_f(p)
}

/// Regular text with the syntax highlighting of a program keyword.
fn keyword(s: &str) -> Doc {
    intensify(
        ConsoleIntensity::Bold,
        color(
            ConsoleLayer::Foreground,
            ColorIntensity::Vivid,
            Color::Blue,
            text(s),
        ),
    )
}

/// Program operator (`operator`).
fn maybe_operator(s: &str) -> Doc {
    color(
        ConsoleLayer::Foreground,
        ColorIntensity::Dull,
        Color::White,
        text(s),
    )
}

/// Dull white document (`parenDoc`).
fn paren_doc(d: Doc) -> Doc {
    color(
        ConsoleLayer::Foreground,
        ColorIntensity::Dull,
        Color::White,
        d,
    )
}

/// Bold document (`special`).
fn special(s: &str) -> Doc {
    intensify(ConsoleIntensity::Bold, text(s))
}

/// Cyan integer literal (`intLiteral`).
fn int_literal(i: i64) -> Doc {
    color(
        ConsoleLayer::Foreground,
        ColorIntensity::Dull,
        Color::Cyan,
        i.pretty(),
    )
}

/// Red document (`errorDoc`).
#[must_use]
pub fn error_doc(d: Doc) -> Doc {
    color(
        ConsoleLayer::Foreground,
        ColorIntensity::Vivid,
        Color::Red,
        d,
    )
}

/// Parentheses in the dull white color (`hlParens`).
#[must_use]
pub fn hl_parens(d: Doc) -> Doc {
    enclose(paren_doc(lparen()), paren_doc(rparen()), d)
}

/// Braces in the dull white color (`hlBraces`).
#[must_use]
pub fn hl_braces(d: Doc) -> Doc {
    enclose(paren_doc(lbrace()), paren_doc(rbrace()), d)
}

/// Angles in the dull white color (`hlAngles`).
#[must_use]
pub fn hl_angles(d: Doc) -> Doc {
    enclose(paren_doc(langle()), paren_doc(rangle()), d)
}

/// Brackets in the dull white color (`hlBrackets`).
#[must_use]
pub fn hl_brackets(d: Doc) -> Doc {
    enclose(paren_doc(lbracket()), paren_doc(rbracket()), d)
}

/// Conditionally enclose in highlighted parentheses (`condHlParens`).
#[must_use]
pub fn cond_hl_parens(b: bool, d: Doc) -> Doc {
    if b {
        hl_parens(d)
    } else {
        d
    }
}

/// Pretty-printed program with syntax highlighting (`prettyProgram`).
fn pretty_program_f<T: Pretty>(p: &Program<T>) -> Doc {
    let opt_parens = |p: &Program<T>| match &p.content {
        BareProgram::PSymbol(_) => pretty_program_f(p),
        BareProgram::PHole => pretty_program_f(p),
        _ => hl_parens(pretty_program_f(p)),
    };
    match &p.content {
        BareProgram::PSymbol(s) => match as_integer(s) {
            Some(n) => int_literal(n),
            None => {
                if s == VALUE_VAR_NAME {
                    special(s)
                } else {
                    text(s)
                }
            }
        },
        BareProgram::PApp(f, x) => {
            let prefix = hang(TAB, soft_break(pretty_program_f(f), opt_parens(x)));
            match &f.content {
                BareProgram::PSymbol(name) => {
                    if crate::tokens::un_op_tokens()
                        .iter()
                        .any(|(_, t)| *t == name)
                    {
                        hang(TAB, hsp(maybe_operator(name), opt_parens(x)))
                    } else {
                        prefix
                    }
                }
                BareProgram::PApp(g, y) => match &g.content {
                    BareProgram::PSymbol(name) => {
                        if crate::tokens::bin_op_tokens()
                            .iter()
                            .any(|(_, t)| *t == name)
                        {
                            hang(
                                TAB,
                                soft_break(
                                    opt_parens(y),
                                    soft_break(maybe_operator(name), opt_parens(x)),
                                ),
                            )
                        } else {
                            prefix
                        }
                    }
                    _ => prefix,
                },
                _ => prefix,
            }
        }
        BareProgram::PFun(x, e) => {
            let binds = beside(maybe_operator("\\"), hsp(text(x), maybe_operator(".")));
            nest(2, soft_break(binds, pretty_program_f(e)))
        }
        BareProgram::PIf(c, t, e) => {
            let if_doc = hsp(keyword("if"), pretty_program_f(c));
            let then_doc = hang(TAB, soft_break(keyword("then"), pretty_program_f(t)));
            let else_doc = hang(TAB, soft_break(keyword("else"), pretty_program_f(e)));
            beside(linebreak(), hang(TAB, vsp(if_doc, vsp(then_doc, else_doc))))
        }
        BareProgram::PMatch(s, cases) => {
            let head = hsp(hsp(keyword("match"), pretty_program_f(s)), keyword("with"));
            let body = vsep(cases.iter().map(|c| pretty_case(c)).collect());
            beside(linebreak(), hang(TAB, vsp(head, body)))
        }
        BareProgram::PFix(_, e) => pretty_program_f(e),
        BareProgram::PLet(x, e, e2) => {
            // `withType doc t = doc` in the reference: the type is not shown.
            let bind = hang(
                TAB,
                soft_break(
                    hsp(
                        hsp(keyword("let"), text(x)),
                        soft_break(maybe_operator("="), pretty_program_f(e)),
                    ),
                    keyword("in"),
                ),
            );
            beside(linebreak(), vsp(align(bind), pretty_program_f(e2)))
        }
        BareProgram::PHole => {
            if show_doc(&p.type_of.pretty()) == DONT_CARE {
                maybe_operator("??")
            } else {
                hl_parens(hsp(maybe_operator("?? ::"), p.type_of.pretty()))
            }
        }
        BareProgram::PErr => keyword("error"),
    }
}

impl<T: Pretty> Pretty for Program<T> {
    fn pretty(&self) -> Doc {
        pretty_program_f(self)
    }
}

impl Pretty for MeasureCase {
    fn pretty(&self) -> Doc {
        let args: Vec<Doc> = self.arg_names.iter().map(|a| text(a)).collect();
        hsp(
            hsp(text(&self.constructor), hsep(args)),
            hsp(text("->"), self.body.pretty()),
        )
    }
}

/// Pretty-print the constant argument defaults of a measure
/// (`prettyMeasureDefaults`).
#[must_use]
pub fn pretty_measure_defaults(args: &[(Id, Sort)]) -> Doc {
    fn punctuate_end(op: Doc, ds: Vec<Doc>) -> Doc {
        let mut it = ds.into_iter();
        let Some(head) = it.next() else {
            return empty();
        };
        let rest: Vec<Doc> = it.collect();
        if rest.is_empty() {
            hsp(head, op)
        } else {
            hsp(hsp(head, op.clone()), punctuate_end(op, rest))
        }
    }
    let pairs: Vec<Doc> = args
        .iter()
        .map(|(v, s)| hsp(text(v), hsp(maybe_operator(":"), s.pretty())))
        .collect();
    punctuate_end(maybe_operator("->"), pairs)
}

impl Pretty for MeasureDef {
    fn pretty(&self) -> Doc {
        let header = hsp(
            hsp(
                hsp(
                    pretty_measure_defaults(&self.constant_args),
                    self.in_sort.pretty(),
                ),
                text("->"),
            ),
            braces(self.postcondition.pretty()),
        );
        let cases = vsep(self.definitions.iter().map(|d| d.pretty()).collect());
        nest(2, vsp(header, cases))
    }
}

/// Pretty-printed environment assumptions (`prettyAssumptions`).
fn pretty_assumptions(env: &Environment) -> Doc {
    comma_sep(env.assumptions.iter().map(|a| a.pretty()).collect())
}

/// Pretty-printed environment bindings (`prettyBindings`).
fn pretty_bindings(env: &Environment) -> Doc {
    let bindings = remove_domain(&env.constants, &all_symbols(env));
    comma_sep(bindings.keys().map(|k| text(k)).collect())
}

impl Pretty for Environment {
    fn pretty(&self) -> Doc {
        hsp(pretty_bindings(self), pretty_assumptions(self))
    }
}

/// Pretty-printed sort constraint (`prettySortConstraint`).
#[must_use]
pub fn pretty_sort_constraint(c: &SortConstraint) -> Doc {
    match c {
        SortConstraint::SameSort(sl, sr) => hsp(hsp(sl.pretty(), text("=")), sr.pretty()),
        SortConstraint::IsOrd(s) => hsp(text("Ord"), s.pretty()),
    }
}

impl Pretty for SortConstraint {
    fn pretty(&self) -> Doc {
        pretty_sort_constraint(self)
    }
}

impl std::fmt::Display for SortConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", show_doc(&self.pretty()))
    }
}

/// Pretty-printed typing constraint (`prettyConstraint`).
#[must_use]
pub fn pretty_constraint(c: &Constraint) -> Doc {
    match c {
        Constraint::Subtype(env, t1, t2, false, label) => hsp(
            hsp(
                hsp(
                    hsp(env.pretty(), maybe_operator("|-")),
                    hsp(t1.pretty(), maybe_operator("<:")),
                ),
                t2.pretty(),
            ),
            parens(text(label)),
        ),
        Constraint::Subtype(env, t1, t2, true, label) => hsp(
            hsp(
                hsp(
                    hsp(env.pretty(), maybe_operator("|-")),
                    hsp(t1.pretty(), maybe_operator("/\\")),
                ),
                t2.pretty(),
            ),
            parens(text(label)),
        ),
        Constraint::WellFormed(env, t) => {
            hsp(pretty_bindings(env), hsp(maybe_operator("|-"), t.pretty()))
        }
        Constraint::WellFormedCond(env, c) => {
            hsp(pretty_bindings(env), hsp(maybe_operator("|-"), c.pretty()))
        }
        Constraint::WellFormedMatchCond(env, c) => hsp(
            pretty_bindings(env),
            hsp(maybe_operator("|- (match)"), c.pretty()),
        ),
        Constraint::WellFormedPredicate(_, sorts, p) => {
            let arrows: Vec<Doc> = sorts
                .iter()
                .map(|s| hsp(s.pretty(), maybe_operator("->")))
                .collect();
            hsp(
                hsp(maybe_operator("|-"), p.pretty()),
                hsp(
                    maybe_operator("::"),
                    hsp(hsep(arrows), Sort::BoolS.pretty()),
                ),
            )
        }
    }
}

impl Pretty for Constraint {
    fn pretty(&self) -> Doc {
        pretty_constraint(self)
    }
}

impl Pretty for Candidate {
    fn pretty(&self) -> Doc {
        let sizes = parens(hsp(
            self.valid_constraints.len().pretty(),
            self.invalid_constraints.len().pretty(),
        ));
        hsp(
            hsp(beside(text(&self.label), text(":")), self.solution.pretty()),
            sizes,
        )
    }
}

impl Pretty for Goal {
    fn pretty(&self) -> Doc {
        let g = self;
        let lhs = hsp(
            hsp(
                hsp(g.g_environment.pretty(), maybe_operator("|-")),
                hsp(text(&g.g_name), maybe_operator("::")),
            ),
            g.g_spec.pretty(),
        );
        let impl_doc = hsp(hsp(text(&g.g_name), maybe_operator("=")), g.g_impl.pretty());
        let depth = parens(hsp(text("depth:"), g.g_depth.pretty()));
        vsp(lhs, vsp(impl_doc, depth))
    }
}

/// Pretty-printed specification of a goal (`prettySpec`).
#[must_use]
pub fn pretty_spec(g: &Goal) -> Doc {
    hsp(
        text(&g.g_name),
        hsp(maybe_operator("::"), unresolved_spec(g).pretty()),
    )
}

/// Pretty-printed solution of a goal (`prettySolution`).
pub fn pretty_solution<T: Pretty>(g: &Goal, prog: &Program<T>) -> Doc {
    soft_break(hsp(text(&g.g_name), maybe_operator("=")), prog.pretty())
}

impl Pretty for ConstructorSig {
    fn pretty(&self) -> Doc {
        hsp(text(&self.name), hsp(text("::"), self.rtype.pretty()))
    }
}

/// Pretty-printed predicate parameter `predSig` (and its variance flag)
/// (`prettyVarianceParam`).
#[must_use]
pub fn pretty_variance_param(pred_sig: &PredSig, contra: bool) -> Doc {
    let sig = pred_sig.pretty();
    if contra {
        beside(sig, UnOp::Not.pretty())
    } else {
        sig
    }
}

impl Pretty for BareDeclaration {
    fn pretty(&self) -> Doc {
        match self {
            BareDeclaration::TypeDecl(name, tvs, t) => {
                let vars: Vec<Doc> = tvs.iter().map(|v| text(v)).collect();
                hsp(
                    hsp(hsp(keyword("type"), text(name)), hsep(vars)),
                    hsp(maybe_operator("="), t.pretty()),
                )
            }
            BareDeclaration::QualifierDecl(fmls) => hsp(
                keyword("qualifier"),
                hl_braces(comma_sep(fmls.iter().map(|f| f.pretty()).collect())),
            ),
            BareDeclaration::FuncDecl(name, t) => {
                hsp(text(name), hsp(maybe_operator("::"), t.pretty()))
            }
            BareDeclaration::DataDecl(name, t_params, p_params, ctors) => {
                let tps: Vec<Doc> = t_params.iter().map(|v| text(v)).collect();
                let pps: Vec<Doc> = p_params
                    .iter()
                    .map(|(sig, contra)| pretty_variance_param(sig, *contra))
                    .collect();
                let header = hsp(
                    hsp(hsp(hsp(keyword("data"), text(name)), hsep(tps)), hsep(pps)),
                    keyword("where"),
                );
                let ctors = vsep(ctors.iter().map(|c| c.pretty()).collect());
                hang(TAB, vsp(header, ctors))
            }
            BareDeclaration::MeasureDecl(name, in_sort, out_sort, post, cases, args, is_term) => {
                let header = hsp(
                    hsp(
                        hsp(
                            hsp(
                                hsp(option(*is_term, keyword("termination")), keyword("measure")),
                                text(name),
                            ),
                            hsp(maybe_operator("::"), pretty_measure_defaults(args)),
                        ),
                        in_sort.pretty(),
                    ),
                    hsp(
                        maybe_operator("->"),
                        if *post == ftrue() {
                            out_sort.pretty()
                        } else {
                            hsp(
                                hl_braces(hsp(
                                    hsp(out_sort.pretty(), maybe_operator("|")),
                                    post.pretty(),
                                )),
                                keyword("where"),
                            )
                        },
                    ),
                );
                let cases = vsep(cases.iter().map(|c| c.pretty()).collect());
                hang(TAB, vsp(header, cases))
            }
            BareDeclaration::PredDecl(_sig) => {
                panic!("pretty: PredDecl is not handled by the reference Pretty instance")
            }
            BareDeclaration::SynthesisGoal(name, impl_doc) => {
                hsp(text(name), hsp(maybe_operator("="), impl_doc.pretty()))
            }
            BareDeclaration::MutualDecl(names) => {
                let ns: Vec<Doc> = names.iter().map(|n| text(n)).collect();
                hsp(keyword("mutual"), comma_sep(ns))
            }
            BareDeclaration::InlineDecl(name, args, body) => {
                let as_: Vec<Doc> = args.iter().map(|a| text(a)).collect();
                hsp(
                    hsp(hsp(keyword("inline"), text(name)), hsep(as_)),
                    hsp(maybe_operator("="), body.pretty()),
                )
            }
        }
    }
}

impl<A: Pretty> Pretty for Pos<A> {
    fn pretty(&self) -> Doc {
        self.node.pretty()
    }
}

/// Pretty-printed error message (`prettyError`).
#[must_use]
pub fn pretty_error_msg(e: &ErrorMessage) -> Doc {
    let src = |suffix: &str| {
        let parts = match e.kind {
            ErrorKind::ParseError => {
                vec![
                    text(&e.position.source_name),
                    e.position.source_line().pretty(),
                    e.position.source_column().pretty(),
                    text(suffix),
                ]
            }
            ErrorKind::ResolutionError => {
                vec![
                    text(&e.position.source_name),
                    e.position.source_line().pretty(),
                    text(suffix),
                ]
            }
            _ => {
                vec![
                    text(&e.position.source_name),
                    e.position.source_line().pretty(),
                    text(suffix),
                ]
            }
        };
        error_doc(hcat(
            parts.into_iter().map(|p| beside(p, colon())).collect(),
        ))
    };
    let head = match e.kind {
        ErrorKind::ParseError => src(" Parse Error"),
        ErrorKind::ResolutionError => src(" Resolution Error"),
        _ => src(" Error"),
    };
    let descr = e.description.pretty();
    match e.kind {
        ErrorKind::ParseError => align(hang(TAB, vsp(head, descr))),
        _ => hang(TAB, vsp(head, descr)),
    }
}

impl Pretty for ErrorMessage {
    fn pretty(&self) -> Doc {
        pretty_error_msg(self)
    }
}

impl std::fmt::Display for ErrorMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", show_doc(&self.pretty()))
    }
}

/// Entry of a map: `key -> value`, appearing in the output of `hMapDoc` and
/// `vMapDoc` (`entryDoc`).
fn entry_doc<K: Pretty, V: Pretty>(k: &K, v: &V) -> Doc {
    nest(2, hsp(hsp(k.pretty(), text("->")), v.pretty()))
}

/// Pretty-printed map, enclosed in brackets (`hMapDoc`).
#[must_use]
pub fn h_map_doc<K: Pretty, V: Pretty>(m: &BTreeMap<K, V>) -> Doc {
    let entries: Vec<Doc> = m.iter().map(|(k, v)| entry_doc(k, v)).collect();
    brackets(comma_sep(entries))
}

/// Pretty-printed map, one entry per line (`vMapDoc`).
#[must_use]
pub fn v_map_doc<K: Pretty, V: Pretty>(m: &BTreeMap<K, V>) -> Doc {
    let entries: Vec<Doc> = m.iter().map(|(k, v)| entry_doc(k, v)).collect();
    vsep(entries)
}

/// Prints data in a table, with fixed column widths. Positive widths for
/// left justification, negative for right (`mkTable`).
#[must_use]
pub fn mk_table(widths: &[isize], docs: &[Vec<Doc>]) -> Doc {
    vsep(
        docs.iter()
            .map(|row| {
                let filled: Vec<Doc> = widths
                    .iter()
                    .zip(row.iter())
                    .map(|(w, d)| {
                        if *w < 0 {
                            lfill(isize_to_usize(-w), d.clone())
                        } else {
                            fill(isize_to_usize(*w), d.clone())
                        }
                    })
                    .collect();
                hsep(filled)
            })
            .collect(),
    )
}

/// Table with LaTeX column separators (`mkTableLaTeX`).
#[must_use]
pub fn mk_table_latex(widths: &[isize], docs: &[Vec<Doc>]) -> Doc {
    let mut new_widths = Vec::new();
    for (i, w) in widths.iter().enumerate() {
        if i > 0 {
            new_widths.push(3);
        }
        new_widths.push(*w);
    }
    new_widths.push(3);
    let mut rows: Vec<Vec<Doc>> = Vec::new();
    for row in docs {
        let mut row_docs = Vec::new();
        for (i, d) in row.iter().enumerate() {
            if i > 0 {
                row_docs.push(text(" &"));
            }
            row_docs.push(d.clone());
        }
        row_docs.push(text(" \\\\"));
        rows.push(row_docs);
    }
    mk_table(&new_widths, &rows)
}

/// Size of a formula in AST nodes (`fmlNodeCount`).
pub fn fml_node_count(fml: &Formula) -> usize {
    match fml {
        Formula::SetLit(_, args) => 1 + args.iter().map(fml_node_count).sum::<usize>(),
        Formula::Unary(_, e) => 1 + fml_node_count(e),
        Formula::Binary(_, l, r) => 1 + fml_node_count(l) + fml_node_count(r),
        Formula::Ite(c, l, r) => 1 + fml_node_count(c) + fml_node_count(l) + fml_node_count(r),
        Formula::Pred(_, _, args) | Formula::Cons(_, _, args) => {
            1 + args.iter().map(fml_node_count).sum::<usize>()
        }
        Formula::All(_, e) => 1 + fml_node_count(e),
        _ => 1,
    }
}

fn fml_node_count_ftrue(fml: &Formula) -> usize {
    match fml {
        Formula::BoolLit(_) => 0,
        _ => fml_node_count(fml),
    }
}

/// Cumulative size of all refinements in a type (`typeNodeCount`).
pub fn type_node_count(t: &RType) -> usize {
    match t {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(_, t_args, p_args), fml) => {
            fml_node_count_ftrue(fml)
                + t_args.iter().map(type_node_count).sum::<usize>()
                + p_args.iter().map(fml_node_count_ftrue).sum::<usize>()
        }
        TypeSkeleton::ScalarT(_, fml) => fml_node_count_ftrue(fml),
        TypeSkeleton::FunctionT(_, t_arg, t_res) => type_node_count(t_arg) + type_node_count(t_res),
        _ => panic!("typeNodeCount: not a scalar or function type"),
    }
}

/// Size of a program in AST nodes (`programNodeCount`).
#[must_use]
pub fn program_node_count(p: &Program<RType>) -> usize {
    match &p.content {
        BareProgram::PSymbol(_) => 1,
        BareProgram::PApp(e1, e2) => 1 + program_node_count(e1) + program_node_count(e2),
        BareProgram::PFun(_, e) => 1 + program_node_count(e),
        BareProgram::PIf(c, e1, e2) => {
            1 + program_node_count(c) + program_node_count(e1) + program_node_count(e2)
        }
        BareProgram::PMatch(e, cases) => {
            1 + program_node_count(e)
                + cases
                    .iter()
                    .map(|c| program_node_count(&c.expr))
                    .sum::<usize>()
        }
        BareProgram::PFix(_, e) => program_node_count(e),
        BareProgram::PLet(_, e, e2) => 1 + program_node_count(e) + program_node_count(e2),
        BareProgram::PHole => 0,
        BareProgram::PErr => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        logic::{eq, fnot, gt, int_lit, or, val_bool, val_int},
        program::{u_hole, untyped},
        types::{bool_all, int_all, set_all, vart_all},
    };

    fn show(d: &Doc) -> String {
        // Plain rendering (no SGR codes) at the default width.
        display(&render_pretty(0.4, 80, &plain(d)))
    }

    #[test]
    fn basic_concatenation() {
        assert_eq!(show(&hsp(text("a"), text("b"))), "a b");
        assert_eq!(show(&vsp(text("a"), text("b"))), "a\nb");
        assert_eq!(show(&hcat(vec![text("a"), text("b"), text("c")])), "abc");
    }

    #[test]
    fn empty_aware_separators() {
        let d = hsp(text("a"), hsp(empty(), text("b")));
        assert_eq!(show(&d), "a b");
        let d = hsp(empty(), text("b"));
        assert_eq!(show(&d), "b");
        assert!(is_empty(&empty()));
        assert!(!is_empty(&text("x")));
        assert!(!is_empty(&linebreak()));
    }

    #[test]
    fn linebreak_flattens_to_empty() {
        // linebreak under group behaves like empty.
        let d = group(hcat(vec![text("a"), linebreak(), text("b")]));
        assert_eq!(show(&d), "ab");
        // and line under group behaves like a space.
        let d = group(hcat(vec![text("a"), line(), text("b")]));
        assert_eq!(show(&d), "a b");
    }

    #[test]
    fn group_breaks_when_too_wide() {
        let d = group(vcat(vec![
            text("hello"),
            text("some-long-line-that-does-not-fit"),
        ]));
        assert_eq!(show(&d), "hello\nsome-long-line-that-does-not-fit");
    }

    #[test]
    fn nesting_indents_lines() {
        let d = hcat(vec![text("a"), nest(2, hcat(vec![linebreak(), text("b")]))]);
        assert_eq!(show(&d), "a\n  b");
    }

    #[test]
    fn align_sets_nesting_to_column() {
        // A (hard) linebreak inside `align` indents to the current column.
        let d = beside(text("ab"), align(hcat(vec![linebreak(), text("c")])));
        assert_eq!(show(&d), "ab\n  c");
        let d = align(vcat(vec![text("c"), text("d")]));
        assert_eq!(show(&d), "c\nd");
    }

    #[test]
    fn enclose_sep_lays_out_vertically() {
        // Mirrors the reference doc example: `text "list" <+> (list ...)`.
        let d = hsp(
            text("list"),
            enclose_sep(
                &lparen(),
                &rparen(),
                &comma(),
                vec![text("a"), text("some-very-long-element-that-does-not-fit")],
            ),
        );
        // "(a,some...)" is longer than the ribbon width (0.4 * 80), so break;
        // separators are glued to the front of following elements.
        let s = show(&d);
        assert_eq!(
            s,
            "list (a\n     ,some-very-long-element-that-does-not-fit)"
        );
    }

    #[test]
    fn enclose_sep_lays_out_horizontally() {
        let d = enclose_sep(&lparen(), &rparen(), &comma(), vec![text("a"), text("b")]);
        assert_eq!(show(&d), "(a,b)");
    }

    #[test]
    fn fill_and_lfill() {
        let d = fill(6, text("ab"));
        assert_eq!(show(&d), "ab    ");
        let d = lfill(6, text("ab"));
        assert_eq!(show(&d), "    ab");
        // fillBreak emits a linebreak at the given indentation if the text
        // does not fit.
        let d = fill_break(6, text("a-very-long-piece"));
        assert_eq!(show(&d), "a-very-long-piece\n      ");
    }

    #[test]
    fn plain_strips_colors() {
        let d = error_doc(text("boo"));
        let colored = show_doc(&d);
        assert!(colored.contains("\u{1b}["));
        assert_eq!(show(&d), "boo");
    }

    #[test]
    fn formula_precedence() {
        use crate::logic::{gt, le, minus, times, val_int};
        let f = or(times(val_int(), int_lit(2)), minus(val_int(), int_lit(1)));
        let s = show(&f.pretty());
        // * binds tighter than +
        assert_eq!(s, "_v * 2 || _v - 1");
        let g = le(val_int(), minus(int_lit(1), int_lit(2)));
        assert_eq!(show(&g.pretty()), "_v <= 1 - 2");
        let h = gt(val_int(), times(int_lit(1), int_lit(2)));
        assert_eq!(show(&h.pretty()), "_v > 1 * 2");
    }

    #[test]
    fn formula_full_parenthesization() {
        let f = or(gt(val_int(), int_lit(0)), eq(val_int(), int_lit(0)));
        assert_eq!(show(&f.pretty()), "_v > 0 || _v == 0");
        // Unary binds tighter than binary.
        let g = fnot(crate::logic::val_bool());
        assert_eq!(show(&g.pretty()), "!_v");
    }

    #[test]
    fn set_literal_brackets() {
        let s = Formula::SetLit(Box::new(Sort::IntS), vec![int_lit(1), int_lit(2)]);
        assert_eq!(show(&s.pretty()), "[1, 2]");
    }

    #[test]
    fn type_pretty() {
        use crate::types::refine_sort;
        let t = int_all();
        assert_eq!(show(&t.pretty()), "Int");
        let t = bool_all();
        // {Bool | true} prints as plain `Bool`.
        assert_eq!(show(&t.pretty()), "Bool");
        let t = TypeSkeleton::FunctionT(
            "x".to_string(),
            Box::new(int_all()),
            Box::new(refine_sort(&Sort::IntS, gt(val_int(), int_lit(0)))),
        );
        assert_eq!(show(&t.pretty()), "x:Int -> {Int|_v > 0}");
        let t = set_all("a");
        assert_eq!(show(&t.pretty()), "DSet a");
    }

    #[test]
    fn pretty_hole_is_question_mark() {
        let p = u_hole();
        assert_eq!(show(&p.pretty()), "??");
    }

    #[test]
    fn program_infix_operators() {
        use crate::program::{erase_types, fml_to_program};
        let fml = eq(val_int(), int_lit(3));
        let p = erase_types(&fml_to_program(&fml));
        // Binary operator in infix notation.
        assert_eq!(show(&p.pretty()), "_v == 3");
        // Unary operator in prefix notation (`<+>` adds a space).
        let p = fml_to_program(&fnot(val_bool()));
        assert_eq!(show(&p.pretty()), "! _v");
    }

    #[test]
    fn pretty_bare_declaration_type() {
        let d =
            BareDeclaration::TypeDecl("MyType".to_string(), vec!["a".to_string()], vart_all("a"));
        assert_eq!(show(&d.pretty()), "type MyType a = a");
    }

    #[test]
    fn nice_counting() {
        let f = crate::logic::eq(crate::logic::val_int(), int_lit(0));
        assert_eq!(fml_node_count(&f), 3);
        let t = TypeSkeleton::ScalarT(
            crate::types::BaseType::IntT,
            crate::logic::eq(crate::logic::val_int(), int_lit(0)),
        );
        assert_eq!(type_node_count(&t), 3);
        assert_eq!(
            program_node_count(&untyped(BareProgram::PSymbol("x".to_string()))),
            1
        );
    }
}
