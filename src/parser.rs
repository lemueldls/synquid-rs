//! Parser for Synquid's program specification DSL (mirror of `Synquid.Parser`).
//!
//! The reference parser uses Parsec with `Text.Parsec.Indent` for
//! indentation-sensitive grammar.  This port uses a hand-written lexer that
//! records source positions for every token plus an indentation-reference
//! column that mirrors `withPos`/`indented`/`sameOrIndented`/`block` from
//! the `indents` package:
//!
//! * `withPos p` sets the indentation reference to the current position and
//!   then runs `p`; the reference is restored afterwards (the change is scoped
//!   to `p`, as in indents' `local (const p)`).
//! * `block p` captures the current column as a local reference and parses one
//!   or more `p` items that start at exactly that column; the implicit
//!   reference is left untouched.
//! * `indented` fails unless the current column is strictly greater than the
//!   reference column.
//! * `sameOrIndented` fails unless the current token is on the reference line
//!   or at a column strictly greater than the reference column.

use std::collections::BTreeMap;

use crate::{
    error::{ErrorKind, ErrorMessage, Pos, SourcePos},
    logic::{ffalse, ftrue, int_lit, BinOp, Formula, PredSig, Sort, UnOp, DONT_CARE},
    pretty::text,
    program::{
        untyped, BareDeclaration, BareProgram, Case, ConstructorSig, Declaration, MeasureCase,
        Program,
    },
    tokens::{bin_op_tokens, keywords, other_ops, un_op_tokens, COMMENT_START},
    types::{arity, BaseType, RSchema, RType, SchemaSkeleton, TypeSkeleton},
    util::Id,
};

/// One lexeme with its source position (1-based line and column; tabs count
/// as a single column, mirroring Parsec's `SourcePos`).
#[derive(Clone, Debug)]
pub(crate) struct Tok {
    pub text: String,
    pub line: usize,
    pub col: usize,
}

impl Tok {
    fn pos(&self, source_name: &str) -> SourcePos {
        SourcePos {
            source_name: source_name.to_string(),
            line: self.line,
            column: self.col,
        }
    }
}

/// Is the token text shaped like an identifier (mirrors `Text.Parsec.Token`
/// `identifier`, which matches only identifier lexemes)?
fn is_ident_text(text: &str) -> bool {
    let mut cs = text.chars();
    match cs.next() {
        Some(c) if is_ident_start(c) => cs.all(is_ident_cont),
        _ => false,
    }
}

/// Is the token an identifier (i.e. starts with a letter, `_` or `'`)?
fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_' || c == '\''
}

/// Is the token an identifier continuation character?
fn is_ident_cont(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Characters that may start an operator lexeme.  Mirrors the reference's
/// `opNames = unOpTokens ++ (binOpTokens \\ keywords) ++ otherOps`
/// (keywords such as `in` lex as words, never as operators).
fn op_start_chars() -> Vec<char> {
    let mut names = Vec::new();
    for (_, s) in un_op_tokens() {
        names.push(s.to_string());
    }
    for (_, s) in bin_op_tokens() {
        if !is_keyword(s) {
            names.push(s.to_string());
        }
    }
    for s in other_ops() {
        names.push(s.to_string());
    }
    let mut starts: Vec<char> = names.iter().map(|s| s.chars().next().unwrap()).collect();
    starts.sort_unstable();
    starts.dedup();
    starts
}

/// Characters that may continue an operator lexeme.
fn op_letter_chars() -> Vec<char> {
    let mut names = Vec::new();
    for (_, s) in un_op_tokens() {
        names.push(s.to_string());
    }
    for (_, s) in bin_op_tokens() {
        if !is_keyword(s) {
            names.push(s.to_string());
        }
    }
    for s in other_ops() {
        names.push(s.to_string());
    }
    let mut letters: Vec<char> = names.iter().flat_map(|s| s.chars().skip(1)).collect();
    letters.sort_unstable();
    letters.dedup();
    letters
}

/// Keywords, compared case-sensitively (the reference's `synquidDef` sets
/// `caseSensitive = True`, so `True`/`true` are distinct lexemes).
fn is_keyword(text: &str) -> bool {
    keywords().contains(&text)
}

/// Lex `input` into tokens.  Comments and whitespace (including newlines)
/// are discarded, but every token keeps the position of its first character.
pub(crate) fn lex(input: &str, source_name: &str) -> Result<(Vec<Tok>, SourcePos), ErrorMessage> {
    let chars: Vec<char> = input.chars().collect();
    let mut toks = Vec::new();
    let mut line = 1usize;
    let mut col = 1usize;
    let mut i = 0usize;
    let err = |msg: String, line: usize, col: usize| {
        ErrorMessage::new(
            ErrorKind::ParseError,
            SourcePos {
                source_name: source_name.to_string(),
                line,
                column: col,
            },
            text(&msg),
        )
    };
    let op_starts = op_start_chars();
    let op_letters = op_letter_chars();
    let is_op_start = |c: char| op_starts.contains(&c);
    let is_op_letter = |c: char| op_letters.contains(&c);
    while i < chars.len() {
        let c = chars[i];
        match c {
            ' ' | '\t' | '\r' => {
                i += 1;
                col += 1;
            }
            '\n' => {
                i += 1;
                line += 1;
                col = 1;
            }
            '-' if i + 1 < chars.len() && chars[i + 1] == '-' => {
                // Line comment: skip to end of line.
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '{' if i + 1 < chars.len() && chars[i + 1] == '-' => {
                // Block comment (not nested).
                let start_line = line;
                let start_col = col;
                i += 2;
                col += 2;
                let mut closed = false;
                while i < chars.len() {
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    if chars[i] == '-' && i + 1 < chars.len() && chars[i + 1] == '}' {
                        i += 2;
                        col += 1;
                        closed = true;
                        break;
                    }
                    i += 1;
                }
                if !closed {
                    return Err(err(
                        format!("unterminated block comment ({COMMENT_START})"),
                        start_line,
                        start_col,
                    ));
                }
            }
            c if c.is_ascii_digit() => {
                let start_col = col;
                let mut j = i;
                while j < chars.len() && chars[j].is_ascii_digit() {
                    j += 1;
                    col += 1;
                }
                toks.push(Tok {
                    text: chars[i..j].iter().collect(),
                    line,
                    col: start_col,
                });
                i = j;
            }
            c if is_ident_start(c) => {
                let start_col = col;
                let mut j = i;
                while j < chars.len() && is_ident_cont(chars[j]) {
                    j += 1;
                    col += 1;
                }
                toks.push(Tok {
                    text: chars[i..j].iter().collect(),
                    line,
                    col: start_col,
                });
                i = j;
            }
            '(' | ')' | '{' | '}' | '[' | ']' | ',' => {
                toks.push(Tok {
                    text: c.to_string(),
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            c if is_op_start(c) => {
                let start_col = col;
                let mut j = i + 1;
                col += 1;
                while j < chars.len() && is_op_letter(chars[j]) {
                    j += 1;
                    col += 1;
                }
                toks.push(Tok {
                    text: chars[i..j].iter().collect(),
                    line,
                    col: start_col,
                });
                i = j;
            }
            _ => {
                return Err(err(format!("unexpected character '{c}'"), line, col));
            }
        }
    }
    let eof_pos = SourcePos {
        source_name: source_name.to_string(),
        line,
        column: col,
    };
    Ok((toks, eof_pos))
}

/// Internal parse error: message plus the position of the offending token.
#[derive(Clone, Debug)]
struct PErr {
    msg: String,
    pos: SourcePos,
}

type PRes<T> = Result<T, PErr>;

fn perr(pos: SourcePos, msg: impl Into<String>) -> PErr {
    PErr {
        msg: msg.into(),
        pos,
    }
}

#[derive(Debug)]
struct Parser<'a> {
    toks: &'a [Tok],
    idx: usize,
    /// Indentation reference (line, column).
    ref_line: usize,
    ref_col: usize,
    source_name: String,
    eof_pos: SourcePos,
}

impl<'a> Parser<'a> {
    fn new(toks: &'a [Tok], source_name: &str, eof_pos: SourcePos) -> Self {
        Parser {
            toks,
            idx: 0,
            ref_line: 1,
            ref_col: 1,
            source_name: source_name.to_string(),
            eof_pos,
        }
    }

    fn cur(&self) -> Option<&Tok> {
        self.toks.get(self.idx)
    }

    fn pos(&self) -> SourcePos {
        match self.cur() {
            Some(t) => t.pos(&self.source_name),
            None => SourcePos {
                source_name: self.source_name.clone(),
                line: self.eof_pos.line,
                column: self.eof_pos.column,
            },
        }
    }

    const fn skip(&mut self) {
        self.idx += 1;
    }

    /// Save and restore only the input position (like Parsec's `try`): the
    /// indentation reference is intentionally left mutated.
    fn attempt<T>(&mut self, f: impl FnOnce(&mut Self) -> PRes<T>) -> Option<T> {
        let save = self.idx;
        if let Ok(v) = f(self) {
            Some(v)
        } else {
            self.idx = save;
            None
        }
    }

    /// `withPos p`: set the indentation reference to the current position,
    /// run `p`, then restore the previous reference.  The reference change is
    /// scoped to `p` (indents implements `withPos` as `local (const p)`).
    fn with_pos<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<T> {
        let (saved_line, saved_col) = (self.ref_line, self.ref_col);
        if let Some((line, col)) = self.cur().map(|t| (t.line, t.col)) {
            self.ref_line = line;
            self.ref_col = col;
        }
        let r = f(self);
        self.ref_line = saved_line;
        self.ref_col = saved_col;
        r
    }

    /// `indented`: fail unless the current column is greater than the
    /// reference column.
    fn indented(&mut self) -> PRes<()> {
        match self.cur() {
            Some(t) if t.col > self.ref_col => Ok(()),
            Some(_) => Err(perr(self.pos(), "not indented")),
            None => Err(perr(self.pos(), "end of input: expecting indented token")),
        }
    }

    /// `sameOrIndented`: fail unless the current token is on the reference
    /// line, or at a column strictly greater than the reference column.
    fn same_or_indented(&mut self) -> PRes<()> {
        match self.cur() {
            Some(t) if t.line == self.ref_line || t.col > self.ref_col => Ok(()),
            Some(_) => Err(perr(self.pos(), "not same or indented")),
            None => Err(perr(self.pos(), "end of input: expecting token")),
        }
    }

    /// `checkIndent`: fail unless the current column equals the reference
    /// column.
    fn check_indent(&mut self) -> PRes<()> {
        match self.cur() {
            Some(t) if t.col == self.ref_col => Ok(()),
            Some(_) => Err(perr(self.pos(), "indentation mismatch")),
            None => Err(perr(
                self.pos(),
                "end of input: expecting token at same indentation",
            )),
        }
    }

    /// `block p`: capture the current column as a local reference and parse
    /// one or more items starting at exactly that column (indents'
    /// `block = do { ref <- indentation; many1 (checkIndent ref >> p) }`).
    /// The implicit reference is left untouched; items' internal `withPos`
    /// calls are scoped, so the captured reference stays valid across items.
    /// Subsequent items that fail end the block (as in Parsec's `many`).
    fn block_of<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<Vec<T>> {
        let (line, col) = match self.cur() {
            Some(t) => (t.line, t.col),
            None => return Err(perr(self.pos(), "end of input: expecting block")),
        };
        self.check_indent_at(line, col)?;
        let first = self.block_item(line, col, &mut f)?;
        let mut out = vec![first];
        loop {
            match self.cur() {
                Some(t) if t.col == col => {}
                _ => break,
            }
            match self.block_item(line, col, &mut f) {
                Ok(v) => out.push(v),
                Err(_) => break,
            }
        }
        Ok(out)
    }

    /// Run a block item with the block's reference active, restoring the
    /// previous implicit reference afterwards.
    fn block_item<T>(
        &mut self,
        line: usize,
        col: usize,
        f: &mut impl FnMut(&mut Self) -> PRes<T>,
    ) -> PRes<T> {
        let (saved_line, saved_col) = (self.ref_line, self.ref_col);
        self.ref_line = line;
        self.ref_col = col;
        let r = f(self);
        self.ref_line = saved_line;
        self.ref_col = saved_col;
        r
    }

    /// `checkIndent` against an explicit reference: fail unless the current
    /// column equals the reference column.
    fn check_indent_at(&mut self, line: usize, col: usize) -> PRes<()> {
        match self.cur() {
            Some(t) if t.col == col => Ok(()),
            Some(_) => Err(perr(
                self.pos(),
                format!("indentation mismatch (block started at line {line})"),
            )),
            None => Err(perr(
                self.pos(),
                "end of input: expecting token at same indentation",
            )),
        }
    }

    /// `many (sameOrIndented >> p)`: collect items that are on the reference
    /// line or indented beyond it.
    fn same_indented_many<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> Vec<T> {
        let mut out = Vec::new();
        loop {
            if self.same_or_indented().is_err() {
                break;
            }
            match self.attempt(|p| f(p)) {
                Some(v) => out.push(v),
                None => break,
            }
        }
        out
    }

    /// `many1 (sameOrIndented >> p)`: like `same_indented_many`, but
    /// requires at least one item.
    fn same_indented_many1<T>(&mut self, f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<Vec<T>> {
        let out = self.same_indented_many(f);
        if out.is_empty() {
            return Err(perr(self.pos(), "expecting at least one argument"));
        }
        Ok(out)
    }

    fn expect_punct(&mut self, p: &str) -> PRes<()> {
        match self.cur() {
            Some(t) if t.text == p => {
                self.skip();
                Ok(())
            }
            _ => Err(perr(self.pos(), format!("expecting `{p}`"))),
        }
    }

    fn cur_is_kw(&self, kw: &str) -> bool {
        matches!(self.cur(), Some(t) if t.text == kw)
    }

    fn expect_kw(&mut self, kw: &str) -> PRes<()> {
        if self.cur_is_kw(kw) {
            self.skip();
            Ok(())
        } else {
            Err(perr(self.pos(), format!("expecting keyword `{kw}`")))
        }
    }

    fn expect_op(&mut self, op: &str) -> PRes<()> {
        match self.cur() {
            Some(t) if t.text == op => {
                self.skip();
                Ok(())
            }
            _ => Err(perr(self.pos(), format!("expecting `{op}`"))),
        }
    }

    fn cur_is_op(&self, op: &str) -> bool {
        matches!(self.cur(), Some(t) if t.text == op)
    }

    fn cur_is_punct(&self, p: &str) -> bool {
        matches!(self.cur(), Some(t) if t.text == p)
    }

    /// Parse a plain identifier (must be identifier-shaped, not capitalized,
    /// not a keyword, must not be `_`).
    fn expect_identifier(&mut self) -> PRes<Id> {
        let t = match self.cur() {
            Some(t) if is_ident_text(&t.text) && !is_keyword(&t.text) => t,
            _ => return Err(perr(self.pos(), "expecting identifier")),
        };
        if is_type_name(&t.text) {
            return Err(perr(
                self.pos(),
                format!("unexpected capitalized `{}`", t.text),
            ));
        }
        if t.text == DONT_CARE {
            return Err(perr(self.pos(), format!("unexpected blank `{}`", t.text)));
        }
        let name = t.text.clone();
        self.skip();
        Ok(name)
    }

    /// Parse an identifier or the blank `_`.
    fn expect_identifier_or_blank(&mut self) -> PRes<Id> {
        let t = match self.cur() {
            Some(t) if is_ident_text(&t.text) && !is_keyword(&t.text) => t,
            _ => return Err(perr(self.pos(), "expecting identifier or blank")),
        };
        if is_type_name(&t.text) {
            return Err(perr(
                self.pos(),
                format!("unexpected capitalized `{}`", t.text),
            ));
        }
        let name = t.text.clone();
        self.skip();
        Ok(name)
    }

    /// Parse a type name (a capitalized identifier).
    fn expect_type_name(&mut self) -> PRes<Id> {
        let t = match self.cur() {
            Some(t) if is_ident_text(&t.text) && !is_keyword(&t.text) => t,
            _ => return Err(perr(self.pos(), "expecting type name")),
        };
        if !is_type_name(&t.text) {
            return Err(perr(
                self.pos(),
                format!("unexpected non-capitalized `{}`", t.text),
            ));
        }
        let name = t.text.clone();
        self.skip();
        Ok(name)
    }

    fn expect_int(&mut self) -> PRes<i64> {
        let t = match self.cur() {
            Some(t) if t.text.chars().all(|c| c.is_ascii_digit()) => t,
            _ => return Err(perr(self.pos(), "expecting natural number")),
        };
        let n = t
            .text
            .parse::<i64>()
            .map_err(|_| perr(self.pos(), format!("integer literal too large: {}", t.text)))?;
        self.skip();
        Ok(n)
    }

    /// A parenthesized section: `( p )`.
    fn parens<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<T> {
        self.expect_punct("(")?;
        let v = f(self)?;
        self.expect_punct(")")?;
        Ok(v)
    }

    /// A braced section: `{ p }`.
    fn braces<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<T> {
        self.expect_punct("{")?;
        let v = f(self)?;
        self.expect_punct("}")?;
        Ok(v)
    }

    /// An angled section: `< p >`.
    fn angles<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<T> {
        self.expect_op("<")?;
        let v = f(self)?;
        self.expect_op(">")?;
        Ok(v)
    }

    /// A bracketed section: `[ p ]`.
    fn brackets<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<T> {
        self.expect_punct("[")?;
        let v = f(self)?;
        self.expect_punct("]")?;
        Ok(v)
    }

    /// Comma-separated items, allowing an empty list (mirrors `commaSep`).
    fn comma_sep0<T>(&mut self, mut f: impl FnMut(&mut Self) -> PRes<T>) -> PRes<Vec<T>> {
        let mut out = Vec::new();
        if let Some(v) = self.attempt(|p| f(p)) {
            out.push(v);
            while self.attempt(|p| p.expect_punct(",")).is_some() {
                out.push(f(self)?);
            }
        }
        Ok(out)
    }
}

fn is_type_name(name: &str) -> bool {
    name.chars().next().is_some_and(|c| c.is_uppercase())
}

impl Parser<'_> {
    /// `parseDeclaration`: one declaration, with the source position of its
    /// first token attached (as in `attachPosBefore`).
    fn parse_declaration(&mut self) -> PRes<Pos<BareDeclaration>> {
        let position = self.pos();
        let node = self.parse_declaration_body()?;
        Ok(Pos::new(position, node))
    }

    fn parse_declaration_body(&mut self) -> PRes<BareDeclaration> {
        if let Some(d) = self.attempt(|p| p.parse_type_decl()) {
            return Ok(d);
        }
        if let Some(d) = self.attempt(|p| p.parse_data_decl()) {
            return Ok(d);
        }
        if let Some(d) = self.attempt(|p| p.parse_measure_decl()) {
            return Ok(d);
        }
        if let Some(d) = self.attempt(|p| p.parse_pred_decl()) {
            return Ok(d);
        }
        if let Some(d) = self.attempt(|p| p.parse_qualifier_decl()) {
            return Ok(d);
        }
        if let Some(d) = self.attempt(|p| p.parse_mutual_decl()) {
            return Ok(d);
        }
        if let Some(d) = self.attempt(|p| p.parse_inline_decl()) {
            return Ok(d);
        }
        self.parse_func_decl_or_goal()
    }

    /// `parseTypeDecl`: `type name vars = type`.
    fn parse_type_decl(&mut self) -> PRes<BareDeclaration> {
        self.expect_kw("type")?;
        let name = self.expect_type_name()?;
        let vars = self.same_indented_many(|p| p.expect_identifier());
        self.expect_op("=")?;
        let def = self.parse_type()?;
        Ok(BareDeclaration::TypeDecl(name, vars, def))
    }

    /// `parseDataDecl`: `data name tparams (predParams) [where constructors]`.
    fn parse_data_decl(&mut self) -> PRes<BareDeclaration> {
        self.expect_kw("data")?;
        let name = self.expect_type_name()?;
        let tparams = self.same_indented_many(|p| p.expect_identifier());
        let mut pparams = Vec::new();
        loop {
            if self.same_or_indented().is_err() {
                break;
            }
            match self.attempt(|p| {
                let sig = p.angles(|p| p.parse_pred_sig())?;
                let negated = p.attempt(|p| p.expect_op("!")).is_some();
                Ok((sig, negated))
            }) {
                Some(pp) => pparams.push(pp),
                None => break,
            }
        }
        let constructors = match self.attempt(|p| p.expect_kw("where")) {
            Some(()) => {
                self.indented()?;
                self.block_of(|p| p.parse_constructor_sig())?
            }
            None => Vec::new(),
        };
        Ok(BareDeclaration::DataDecl(
            name,
            tparams,
            pparams,
            constructors,
        ))
    }

    /// `parseConstructorSig`: `name :: type`.
    fn parse_constructor_sig(&mut self) -> PRes<ConstructorSig> {
        let constructor = self.expect_type_name()?;
        self.expect_op("::")?;
        let constructor_type = self.parse_type()?;
        Ok(ConstructorSig {
            name: constructor,
            rtype: constructor_type,
        })
    }

    /// `parseMeasureDecl`:
    /// `[termination] measure name :: (arg : sort ->)* sort -> (refinedSort |
    /// sort) [where cases]`.
    fn parse_measure_decl(&mut self) -> PRes<BareDeclaration> {
        let is_termination = self.attempt(|p| p.expect_kw("termination")).is_some();
        self.expect_kw("measure")?;
        let measure_name = self.expect_identifier()?;
        self.expect_op("::")?;
        let mut args = Vec::new();
        loop {
            match self.attempt(|p| {
                let name = p.expect_identifier()?;
                p.expect_op(":")?;
                let sort = p.parse_sort()?;
                p.expect_op("->")?;
                Ok((name, sort))
            }) {
                Some(arg) => args.push(arg),
                None => break,
            }
        }
        let in_sort = self.parse_sort()?;
        self.expect_op("->")?;
        let (out_sort, post) = match self.attempt(|p| p.parse_refined_sort()) {
            Some((s, f)) => (s, f),
            None => (self.parse_sort()?, ftrue()),
        };
        let cases = match self.attempt(|p| p.expect_kw("where")) {
            Some(()) => {
                self.indented()?;
                self.block_of(|p| p.parse_def_case())?
            }
            None => Vec::new(),
        };
        Ok(BareDeclaration::MeasureDecl(
            measure_name,
            in_sort,
            out_sort,
            post,
            cases,
            args,
            is_termination,
        ))
    }

    /// `parseDefCase`: `name binder* -> formula`.
    fn parse_def_case(&mut self) -> PRes<MeasureCase> {
        let constructor = self.expect_type_name()?;
        let arg_names = self.same_indented_many(|p| p.expect_identifier_or_blank());
        self.expect_op("->")?;
        let body = self.parse_formula()?;
        Ok(MeasureCase {
            constructor,
            arg_names,
            body,
        })
    }

    /// `parsePredDecl`: `predicate name :: sorts -> sort`.
    fn parse_pred_decl(&mut self) -> PRes<BareDeclaration> {
        self.expect_kw("predicate")?;
        let sig = self.parse_pred_sig()?;
        Ok(BareDeclaration::PredDecl(sig))
    }

    /// `parseQualifierDecl`: `qualifier {f1, f2, ...}`.
    fn parse_qualifier_decl(&mut self) -> PRes<BareDeclaration> {
        self.expect_kw("qualifier")?;
        let fs = self.braces(|p| p.comma_sep0(|p| p.parse_formula()))?;
        Ok(BareDeclaration::QualifierDecl(fs))
    }

    /// `parseMutualDecl`: `mutual {name1, name2, ...}`.
    fn parse_mutual_decl(&mut self) -> PRes<BareDeclaration> {
        self.expect_kw("mutual")?;
        let ids = self.braces(|p| p.comma_sep0(|p| p.expect_identifier()))?;
        Ok(BareDeclaration::MutualDecl(ids))
    }

    /// `parseInlineDecl`: `inline name arg* = formula`.
    fn parse_inline_decl(&mut self) -> PRes<BareDeclaration> {
        self.expect_kw("inline")?;
        let name = self.expect_identifier()?;
        let args = self.same_indented_many(|p| p.expect_identifier());
        self.expect_op("=")?;
        let body = self.parse_formula()?;
        Ok(BareDeclaration::InlineDecl(name, args, body))
    }

    /// `parseFuncDeclOrGoal`: `name :: schema` or `name = impl`.
    fn parse_func_decl_or_goal(&mut self) -> PRes<BareDeclaration> {
        let name = self.expect_identifier()?;
        if self.attempt(|p| p.expect_op("::")).is_some() {
            let schema = self.parse_schema()?;
            Ok(BareDeclaration::FuncDecl(name, schema))
        } else {
            self.expect_op("=")?;
            let impl_ = self.parse_impl()?;
            Ok(BareDeclaration::SynthesisGoal(name, impl_))
        }
    }
}

impl Parser<'_> {
    /// `parseSchema`: `(<sig> .)* type`.
    fn parse_schema(&mut self) -> PRes<RSchema> {
        if self.cur_is_op("<") {
            let sig = self.angles(|p| p.parse_pred_sig())?;
            self.expect_op(".")?;
            let sch = self.parse_schema()?;
            Ok(SchemaSkeleton::ForallP(sig, Box::new(sch)))
        } else {
            let t = self.parse_type()?;
            Ok(SchemaSkeleton::Monotype(t))
        }
    }

    /// `parseType`.
    fn parse_type(&mut self) -> PRes<RType> {
        self.with_pos(|p| {
            if let Some(t) = p.attempt(|p| p.parse_function_type_with_arg()) {
                Ok(t)
            } else {
                p.parse_function_type_mb()
            }
        })
    }

    /// `parseFunctionTypeWithArg`: `id : argType -> type`.
    fn parse_function_type_with_arg(&mut self) -> PRes<RType> {
        let arg_id = {
            let id = self.expect_identifier()?;
            self.expect_op(":")?;
            id
        };
        let arg_type = match self.attempt(|p| p.parse_unref_type_with_args()) {
            Some(t) => t,
            None => self.parse_type_atom()?,
        };
        self.expect_op("->")?;
        let return_type = self.parse_type()?;
        Ok(TypeSkeleton::FunctionT(
            arg_id,
            Box::new(arg_type),
            Box::new(return_type),
        ))
    }

    /// `parseFunctionTypeMb`: possibly a function type without named args.
    fn parse_function_type_mb(&mut self) -> PRes<RType> {
        let arg_type = match self.attempt(|p| p.parse_unref_type_with_args()) {
            Some(t) => t,
            None => self.parse_type_atom()?,
        };
        if self.attempt(|p| p.expect_op("->")).is_some() {
            let return_type = self.parse_type()?;
            let arg_name = format!("arg{}", arity(&return_type));
            Ok(TypeSkeleton::FunctionT(
                arg_name,
                Box::new(arg_type),
                Box::new(return_type),
            ))
        } else {
            Ok(arg_type)
        }
    }

    /// `parseTypeAtom`.
    fn parse_type_atom(&mut self) -> PRes<RType> {
        if let Some(t) = self.attempt(|p| p.parens(|p| p.parse_type())) {
            return Ok(t);
        }
        if let Some(t) = self.attempt(|p| p.parse_scalar_ref_type()) {
            return Ok(t);
        }
        if let Some(t) = self.attempt(|p| p.parse_unref_type_no_args()) {
            return Ok(t);
        }
        if let Some(t) = self.attempt(|p| p.parse_list_type()) {
            return Ok(t);
        }
        Err(perr(self.pos(), "expecting type"))
    }

    /// `parseUnrefTypeNoArgs`: `Bool`, `Int`, a datatype, or a type variable.
    fn parse_unref_type_no_args(&mut self) -> PRes<RType> {
        if self.cur_is_kw("Bool") {
            self.skip();
            return Ok(TypeSkeleton::ScalarT(BaseType::BoolT, ftrue()));
        }
        if self.cur_is_kw("Int") {
            self.skip();
            return Ok(TypeSkeleton::ScalarT(BaseType::IntT, ftrue()));
        }
        if let Some(name) = self.attempt(|p| p.expect_type_name()) {
            return Ok(TypeSkeleton::ScalarT(
                BaseType::DatatypeT(name, Vec::new(), Vec::new()),
                ftrue(),
            ));
        }
        let name = self.expect_identifier()?;
        Ok(TypeSkeleton::ScalarT(
            BaseType::TypeVarT(BTreeMap::new(), name),
            ftrue(),
        ))
    }

    /// `parseUnrefTypeWithArgs`: `name typeArg* <predArg*>`.
    fn parse_unref_type_with_args(&mut self) -> PRes<RType> {
        let name = self.expect_type_name()?;
        let type_args = self.same_indented_many(|p| p.parse_type_atom());
        let pred_args = self.same_indented_many(|p| p.angles(|p| p.parse_pred_arg()));
        Ok(TypeSkeleton::ScalarT(
            BaseType::DatatypeT(name, type_args, pred_args),
            ftrue(),
        ))
    }

    /// `parsePredArg`: `{formula}` or an identifier naming a predicate.
    fn parse_pred_arg(&mut self) -> PRes<Formula> {
        if self.cur_is_punct("{") {
            let f = self.braces(|p| p.parse_formula())?;
            Ok(f)
        } else {
            let name = self.expect_identifier()?;
            Ok(Formula::Pred(Box::new(Sort::AnyS), name, Vec::new()))
        }
    }

    /// `parseScalarRefType`: `{unrefType | formula}`.
    fn parse_scalar_ref_type(&mut self) -> PRes<RType> {
        self.expect_punct("{")?;
        let t = match self.attempt(|p| p.parse_unref_type_with_args()) {
            Some(t) => t,
            None => self.parse_unref_type_no_args()?,
        };
        let base = match t {
            TypeSkeleton::ScalarT(base, _) => base,
            _ => unreachable!("scalar reference type with non-scalar type"),
        };
        self.expect_op("|")?;
        let refinement = self.parse_formula()?;
        self.expect_punct("}")?;
        Ok(TypeSkeleton::ScalarT(base, refinement))
    }

    /// `parseListType`: `[type]`.
    fn parse_list_type(&mut self) -> PRes<RType> {
        let elem = self.brackets(|p| p.parse_type())?;
        Ok(TypeSkeleton::ScalarT(
            BaseType::DatatypeT("List".to_string(), vec![elem], Vec::new()),
            ftrue(),
        ))
    }

    /// `parsePredSig`: `name :: sort -> ... -> sort`.
    fn parse_pred_sig(&mut self) -> PRes<PredSig> {
        let pred_sig_name = self.expect_identifier()?;
        self.expect_op("::")?;
        let mut sorts = vec![self.parse_sort()?];
        while self.attempt(|p| p.expect_op("->")).is_some() {
            sorts.push(self.parse_sort()?);
        }
        if sorts.len() < 2 {
            return Err(perr(
                self.pos(),
                "expecting `->` between predicate argument sorts",
            ));
        }
        let pred_sig_res_sort = sorts.pop().unwrap();
        let pred_sig_arg_sorts = sorts;
        Ok(PredSig {
            pred_sig_name,
            pred_sig_arg_sorts,
            pred_sig_res_sort,
        })
    }
}

impl Parser<'_> {
    /// `parseSort`.
    fn parse_sort(&mut self) -> PRes<Sort> {
        self.with_pos(|p| {
            if let Some(s) = p.attempt(|p| p.parse_sort_with_args()) {
                Ok(s)
            } else {
                p.parse_sort_atom()
            }
        })
    }

    /// `parseSortAtom`.
    fn parse_sort_atom(&mut self) -> PRes<Sort> {
        if let Some(s) = self.attempt(|p| p.parens(|p| p.parse_sort())) {
            return Ok(s);
        }
        if self.cur_is_kw("Bool") {
            self.skip();
            return Ok(Sort::BoolS);
        }
        if self.cur_is_kw("Int") {
            self.skip();
            return Ok(Sort::IntS);
        }
        if let Some(name) = self.attempt(|p| p.expect_identifier()) {
            return Ok(Sort::VarS(name));
        }
        let name = self.expect_type_name()?;
        Ok(Sort::DataS(name, Vec::new()))
    }

    /// `parseSortWithArgs`: `Set sortAtom` or `name sortAtom*`.
    fn parse_sort_with_args(&mut self) -> PRes<Sort> {
        if self.cur_is_kw("Set") {
            self.skip();
            self.same_or_indented()?;
            let elem = self.parse_sort_atom()?;
            Ok(Sort::SetS(Box::new(elem)))
        } else {
            let name = self.expect_type_name()?;
            let args = self.same_indented_many(|p| p.parse_sort_atom());
            Ok(Sort::DataS(name, args))
        }
    }

    /// `parseRefinedSort`: `{sort | formula}`.
    fn parse_refined_sort(&mut self) -> PRes<(Sort, Formula)> {
        self.braces(|p| {
            let s = p.parse_sort()?;
            p.expect_op("|")?;
            let f = p.parse_formula()?;
            Ok((s, f))
        })
    }
}

impl Parser<'_> {
    /// Operator table, mirroring `exprTable` from the reference parser.
    /// Returns the binary operator (if any) whose token matches the current
    /// position at precedence level `n`.
    fn level_bin_op(&self, member: bool, n: u8) -> Option<BinOp> {
        let t = self.cur()?;

        match (n, t.text.as_str()) {
            (7, "==>") => Some(BinOp::Implies),
            (7, "<==>") => Some(BinOp::Iff),
            (6, "&&") => Some(BinOp::And),
            (6, "||") => Some(BinOp::Or),
            (4, "in") if member => Some(BinOp::Member),
            (4, "==") => Some(BinOp::Eq),
            (4, "!=") => Some(BinOp::Neq),
            (4, "<=") => Some(BinOp::Le),
            (4, "<") => Some(BinOp::Lt),
            (4, ">=") => Some(BinOp::Ge),
            (4, ">") => Some(BinOp::Gt),
            (3, "+") => Some(BinOp::Plus),
            (3, "-") => Some(BinOp::Minus),
            (2, "*") => Some(BinOp::Times),
            _ => None,
        }
    }

    /// `parseFormula`.
    fn parse_formula(&mut self) -> PRes<Formula> {
        self.with_pos(|p| {
            p.parse_expr(
                &mut |p: &mut Parser| p.parse_term(),
                |op, l, r| Formula::Binary(op, Box::new(l), Box::new(r)),
                |op, x| Formula::Unary(op, Box::new(x)),
                true,
            )
        })
    }

    /// `parseTerm`.
    fn parse_term(&mut self) -> PRes<Formula> {
        if self.cur_is_kw("if") {
            self.expect_kw("if")?;
            let e0 = self.parse_formula()?;
            self.expect_kw("then")?;
            let e1 = self.parse_formula()?;
            self.expect_kw("else")?;
            let e2 = self.parse_formula()?;
            return Ok(Formula::Ite(Box::new(e0), Box::new(e1), Box::new(e2)));
        }
        if let Some(f) = self.attempt(|p| p.parse_app_term()) {
            return Ok(f);
        }
        self.parse_atom_term()
    }

    /// `parseAppTerm`: `Cons args...` or `pred args...`.
    fn parse_app_term(&mut self) -> PRes<Formula> {
        if let Some(name) = self.attempt(|p| p.expect_type_name()) {
            let args = self.same_indented_many1(|p| p.parse_atom_term())?;
            return Ok(Formula::Cons(Box::new(Sort::AnyS), name, args));
        }
        let name = self.expect_identifier()?;
        let args = self.same_indented_many1(|p| p.parse_atom_term())?;
        Ok(Formula::Pred(Box::new(Sort::AnyS), name, args))
    }

    /// `parseAtomTerm`.
    fn parse_atom_term(&mut self) -> PRes<Formula> {
        if self.cur_is_punct("(") {
            return self.parens(|p| p.parse_formula());
        }
        if self.cur_is_kw("False") {
            self.skip();
            return Ok(ffalse());
        }
        if self.cur_is_kw("True") {
            self.skip();
            return Ok(ftrue());
        }
        if self
            .cur()
            .is_some_and(|t| t.text.chars().all(|c| c.is_ascii_digit()))
        {
            let n = self.expect_int()?;
            return Ok(int_lit(n));
        }
        if self.cur_is_punct("[") {
            let fs = self.brackets(|p| p.comma_sep0(|p| p.parse_formula()))?;
            return Ok(Formula::SetLit(Box::new(Sort::AnyS), fs));
        }
        if let Some(name) = self.attempt(|p| p.expect_type_name()) {
            return Ok(Formula::Cons(Box::new(Sort::AnyS), name, Vec::new()));
        }
        let name = self.expect_identifier()?;
        Ok(Formula::Var(Box::new(Sort::AnyS), name))
    }
}

impl Parser<'_> {
    /// `parseImpl`.
    fn parse_impl(&mut self) -> PRes<Program<RType>> {
        self.with_pos(|p| {
            if p.cur_is_kw("error") {
                p.expect_kw("error")?;
                return Ok(untyped(BareProgram::PErr));
            }
            if p.cur_is_kw("let") {
                return p.parse_let();
            }
            if p.cur_is_op("\\") {
                return p.parse_fun();
            }
            if p.cur_is_kw("match") {
                return p.parse_match();
            }
            if p.cur_is_kw("if") {
                return p.parse_if();
            }
            p.parse_eterm()
        })
    }

    /// `parseFun`: `\ x . body`.
    fn parse_fun(&mut self) -> PRes<Program<RType>> {
        self.expect_op("\\")?;
        let x = self.expect_identifier_or_blank()?;
        self.expect_op(".")?;
        let body = self.parse_impl()?;
        Ok(untyped(BareProgram::PFun(x, Box::new(body))))
    }

    /// `parseLet`: `let x = e1 in e2`.
    fn parse_let(&mut self) -> PRes<Program<RType>> {
        self.expect_kw("let")?;
        let x = self.expect_identifier_or_blank()?;
        self.expect_op("=")?;
        let e1 = self.parse_impl()?;
        self.expect_kw("in")?;
        let e2 = self.parse_impl()?;
        Ok(untyped(BareProgram::PLet(x, Box::new(e1), Box::new(e2))))
    }

    /// `parseMatch`: `match scrutinee with cases`.
    fn parse_match(&mut self) -> PRes<Program<RType>> {
        self.expect_kw("match")?;
        let scrutinee = self.parse_eterm()?;
        self.expect_kw("with")?;
        self.indented()?;
        let cases = self.block_of(|p| p.parse_match_case())?;
        Ok(untyped(BareProgram::PMatch(Box::new(scrutinee), cases)))
    }

    /// `parseCase` (of a match): `name binder* -> body`.
    fn parse_match_case(&mut self) -> PRes<Case<RType>> {
        let constructor = self.expect_type_name()?;
        let arg_names = self.same_indented_many(|p| p.expect_identifier_or_blank());
        self.expect_op("->")?;
        let body = self.parse_impl()?;
        Ok(Case {
            constructor,
            arg_names,
            expr: body,
        })
    }

    /// `parseIf`: `if cond then t else e`.
    fn parse_if(&mut self) -> PRes<Program<RType>> {
        self.expect_kw("if")?;
        let cond = self.parse_eterm()?;
        self.expect_kw("then")?;
        let then_ = self.parse_impl()?;
        self.expect_kw("else")?;
        let else_ = self.parse_impl()?;
        Ok(untyped(BareProgram::PIf(
            Box::new(cond),
            Box::new(then_),
            Box::new(else_),
        )))
    }

    /// `parseETerm`: expression table over application terms.
    fn parse_eterm(&mut self) -> PRes<Program<RType>> {
        self.parse_expr(
            &mut |p: &mut Parser| p.parse_app_term_eterm(),
            |op, l, r| {
                let symbol = op_to_text(op);
                untyped(BareProgram::PApp(
                    Box::new(untyped(BareProgram::PApp(
                        Box::new(untyped(BareProgram::PSymbol(symbol.to_string()))),
                        Box::new(l),
                    ))),
                    Box::new(r),
                ))
            },
            |op, x| {
                let symbol = unary_op_to_text(op);
                untyped(BareProgram::PApp(
                    Box::new(untyped(BareProgram::PSymbol(symbol.to_string()))),
                    Box::new(x),
                ))
            },
            false,
        )
    }

    /// `parseAppTerm` for elimination terms: application is left-folded.
    fn parse_app_term_eterm(&mut self) -> PRes<Program<RType>> {
        let head = self.parse_atom_term_eterm()?;
        let args = self.same_indented_many(|p| p.parse_app_arg_eterm());
        let mut out = head;
        for arg in args {
            out = untyped(BareProgram::PApp(Box::new(out), Box::new(arg)));
        }
        Ok(out)
    }

    /// One application argument: an atom, or a parenthesized implementation
    /// (with optional type annotation).
    fn parse_app_arg_eterm(&mut self) -> PRes<Program<RType>> {
        if let Some(a) = self.attempt(|p| p.parse_atom_term_eterm()) {
            return Ok(a);
        }
        self.parens(|p| p.parse_impl())
    }

    /// `parseAtomTerm` for elimination terms.
    fn parse_atom_term_eterm(&mut self) -> PRes<Program<RType>> {
        if self.cur_is_punct("(") {
            // withOptionalType: `(impl :: type)` or just `(impl)`.
            return self.parens(|p| {
                let mut program = p.parse_impl()?;
                if p.attempt(|p| p.expect_op("::")).is_some() {
                    program.type_of = p.parse_type()?;
                }
                Ok(program)
            });
        }
        if self.cur_is_op("??") {
            self.skip();
            return Ok(untyped(BareProgram::PHole));
        }
        if self.cur_is_kw("False") {
            self.skip();
            return Ok(untyped(BareProgram::PSymbol("False".to_string())));
        }
        if self.cur_is_kw("True") {
            self.skip();
            return Ok(untyped(BareProgram::PSymbol("True".to_string())));
        }
        if let Some(t) = self.cur()
            && t.text.chars().all(|c| c.is_ascii_digit())
        {
            let text = t.text.clone();
            self.skip();
            return Ok(untyped(BareProgram::PSymbol(text)));
        }
        if self.cur_is_punct("[") {
            // List literal: `[e1, e2, ...]` as Cons applications.
            let elems = self.brackets(|p| p.comma_sep0(|p| p.parse_impl()))?;
            let mut out = untyped(BareProgram::PSymbol("Nil".to_string()));
            for e in elems.into_iter().rev() {
                let cons = untyped(BareProgram::PApp(
                    Box::new(untyped(BareProgram::PSymbol("Cons".to_string()))),
                    Box::new(e),
                ));
                out = untyped(BareProgram::PApp(Box::new(cons), Box::new(out)));
            }
            return Ok(out);
        }
        let name = match self.attempt(|p| p.expect_identifier()) {
            Some(n) => n,
            None => self.expect_type_name()?,
        };
        Ok(untyped(BareProgram::PSymbol(name)))
    }

    /// Generic precedence-climbing expression parser, mirroring
    /// `buildExpressionParser` with the reference operator table.  Level 1
    /// handles prefix operators (at most one per operand), levels 7, 6 and
    /// 2-3 handle right/left-associative binary operators, and levels 4-5
    /// (the latter only when `member` is set) handle non-associative ones.
    fn parse_expr<F, B>(
        &mut self,
        atom: &mut F,
        binop: impl Fn(BinOp, B, B) -> B,
        unop: impl Fn(UnOp, B) -> B,
        member: bool,
    ) -> PRes<B>
    where
        F: FnMut(&mut Self) -> PRes<B>,
    {
        self.parse_expr_level(atom, &binop, &unop, member, 7)
    }

    fn parse_expr_level<F, B>(
        &mut self,
        atom: &mut F,
        binop: &impl Fn(BinOp, B, B) -> B,
        unop: &impl Fn(UnOp, B) -> B,
        member: bool,
        n: u8,
    ) -> PRes<B>
    where
        F: FnMut(&mut Self) -> PRes<B>,
    {
        if n == 1 {
            // Prefix operators, applied at most once.
            let pre = match self.cur() {
                Some(t) if t.text == "!" => Some(UnOp::Not),
                Some(t) if t.text == "-" => Some(UnOp::Neg),
                _ => None,
            };
            let x = if let Some(op) = pre {
                self.skip();
                let x = atom(self)?;
                unop(op, x)
            } else {
                atom(self)?
            };
            return Ok(x);
        }
        let mut x = self.parse_expr_level(atom, binop, unop, member, n - 1)?;
        match n {
            7 | 6 | 3 | 2 => {
                // Left-associative (levels 2, 3, 6) and right-associative
                // (level 7) chains.  The right operand of a right-associative
                // operator is parsed at the same level (chainr1).
                loop {
                    match self.level_bin_op(member, n) {
                        Some(op) => {
                            self.skip();
                            let y = if n == 7 {
                                self.parse_expr_level(atom, binop, unop, member, n)?
                            } else {
                                self.parse_expr_level(atom, binop, unop, member, n - 1)?
                            };
                            x = binop(op, x, y);
                        }
                        None => break,
                    }
                }
            }
            5 | 4 => {
                // Non-associative: at most one operator at this level, and a
                // second one is an ambiguity error.
                if let Some(op) = self.level_bin_op(member, n) {
                    self.skip();
                    let y = self.parse_expr_level(atom, binop, unop, member, n - 1)?;
                    if self.level_bin_op(member, n).is_some() {
                        return Err(perr(
                            self.pos(),
                            "ambiguous use of a non-associative operator",
                        ));
                    }
                    x = binop(op, x, y);
                }
            }
            _ => unreachable!("no operator level {}", n),
        }
        Ok(x)
    }
}

/// The source token for a binary operator.
fn op_to_text(op: BinOp) -> &'static str {
    bin_op_tokens()
        .iter()
        .find(|(o, _)| *o == op)
        .map(|(_, s)| *s)
        .unwrap_or("?")
}

/// The source token for a unary operator.
fn unary_op_to_text(op: UnOp) -> &'static str {
    un_op_tokens()
        .iter()
        .find(|(o, _)| *o == op)
        .map(|(_, s)| *s)
        .unwrap_or("?")
}

/// Parse a complete program, mirroring
/// `parseProgram = whiteSpace *> option [] (block parseDeclaration) <* eof`.
pub fn parse_program(input: &str, source_name: &str) -> Result<Vec<Declaration>, ErrorMessage> {
    let (toks, eof_pos) = lex(input, source_name)?;
    let mut p = Parser::new(&toks, source_name, eof_pos);
    let mut decls = Vec::new();
    let (line, col) = match p.cur() {
        Some(t) => (t.line, t.col),
        None => return Ok(decls),
    };
    p.ref_line = line;
    p.ref_col = col;
    loop {
        if p.check_indent().is_err() {
            break;
        }
        match p.attempt(|p| p.parse_declaration()) {
            Some(d) => decls.push(d),
            None => break,
        }
    }
    if p.cur().is_some() {
        return Err(to_error_message(
            perr(p.pos(), "unexpected input after declarations"),
            source_name,
        ));
    }
    Ok(decls)
}

fn to_error_message(e: PErr, source_name: &str) -> ErrorMessage {
    let _ = source_name;
    ErrorMessage::new(ErrorKind::ParseError, e.pos, text(&e.msg))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        logic::Sort::{BoolS, DataS, IntS, SetS, VarS},
        program::BareProgram::{PApp, PFun, PHole, PIf, PMatch, PSymbol},
        types::BaseType::{BoolT, DatatypeT, IntT},
    };

    fn parse(input: &str) -> Vec<Declaration> {
        parse_program(input, "<test>").unwrap()
    }

    fn parse_err(input: &str) -> ErrorMessage {
        parse_program(input, "<test>").unwrap_err()
    }

    fn is_kw_match(d: &BareDeclaration, kw: &str) -> bool {
        match d {
            BareDeclaration::TypeDecl(..) => kw == "type",
            BareDeclaration::FuncDecl(..) => kw == "func",
            BareDeclaration::DataDecl(..) => kw == "data",
            BareDeclaration::MeasureDecl(..) => kw == "measure",
            BareDeclaration::PredDecl(_) => kw == "predicate",
            BareDeclaration::QualifierDecl(_) => kw == "qualifier",
            BareDeclaration::MutualDecl(_) => kw == "mutual",
            BareDeclaration::InlineDecl(..) => kw == "inline",
            BareDeclaration::SynthesisGoal(..) => kw == "goal",
        }
    }

    const REPLICATE: &str = "\
type Nat = {Int | _v >= 0}

data List a where
\tNil :: List a
\tCons :: x: a -> xs: List a -> List a

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs

zero :: {Int | _v == 0}
inc :: x: Int -> {Int | _v == x + 1}
dec :: x: Int -> {Int | _v == x - 1}
leq :: x: Int -> y: Int -> {Bool | _v == (x <= y)}
neq :: x: Int -> y: Int -> {Bool | _v == (x != y)}

replicate :: n: Nat -> x: a -> {List a | len _v == n}
replicate = ??
";

    const REPLICATE_SOLUTION: &str = "\
type Nat = {Int | _v >= 0}

data List a where
\tNil :: List a
\tCons :: x: a -> xs: List a -> List a

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs

zero :: {Int | _v == 0}
inc :: x: Int -> {Int | _v == x + 1}
dec :: x: Int -> {Int | _v == x - 1}
leq :: x: Int -> y: Int -> {Bool | _v == (x <= y)}
neq :: x: Int -> y: Int -> {Bool | _v == (x != y)}

replicate :: n: Nat -> x: a -> {List a | len _v == n}
replicate = \\n . \\x .
    if n <= 0
      then Nil
      else Cons x (replicate (dec n)
                     x)
";

    const DELETE_SOLUTION: &str = "\
data List a where
\tNil :: List a
\tCons :: x: a -> xs: List a -> List a

termination measure len :: List a -> {Int | _v >= 0} where
  Nil -> 0
  Cons x xs -> 1 + len xs

measure elems :: List a -> Set a where
  Nil -> []
  Cons x xs -> [x] + elems xs

eq :: x: a -> y: a -> {Bool | _v == (x == y)}
neq :: x: a -> y: a -> {Bool | _v == (x != y)}

delete :: x: a -> xs: List a -> {List a | elems _v == elems xs - [x]}
delete = \\x . \\xs .
    match xs with
      Nil -> xs
      Cons x3 x4 ->
        if x3 == x
          then delete x x4
          else Cons x3 (delete x x4)
";

    #[test]
    fn parses_replicate_goal() {
        let decls = parse(REPLICATE);
        assert_eq!(decls.len(), 10);
        assert!(is_kw_match(&decls[0].node, "type"));
        assert!(is_kw_match(&decls[1].node, "data"));
        assert!(is_kw_match(&decls[2].node, "measure"));
        for d in &decls[3..8] {
            assert!(is_kw_match(&d.node, "func"), "{:?}", d.node);
        }
        let goal = &decls[9].node;
        assert!(is_kw_match(goal, "goal"));
        match goal {
            BareDeclaration::SynthesisGoal(name, body) => {
                assert_eq!(name, "replicate");
                assert!(matches!(&body.content, PHole));
            }
            _ => unreachable!(),
        }
        // Positions are attached to declarations.
        assert_eq!(decls[0].position.line, 1);
        assert_eq!(decls[0].position.column, 1);
        assert_eq!(decls[1].position.line, 3);
    }

    #[test]
    fn parses_replicate_solution() {
        let decls = parse(REPLICATE_SOLUTION);
        let goal = &decls[9].node;
        match goal {
            BareDeclaration::SynthesisGoal(_, body) => {
                // \n . \x . if n <= 0 then Nil else Cons x (replicate (dec n) x)
                match &body.content {
                    PFun(n, b1) => {
                        assert_eq!(n, "n");
                        match &b1.content {
                            PFun(x, b2) => {
                                assert_eq!(x, "x");
                                match &b2.content {
                                    PIf(c, t, e) => {
                                        // c = n <= 0
                                        let is_le = |p: &Program<RType>| {
                                            matches!(
                                                &p.content,
                                                PApp(f, _) if matches!(&f.content, PApp(s, l) if
                                                    matches!(&s.content, PSymbol(v) if v == "<=") &&
                                                    matches!(&l.content, PSymbol(v) if v == "n"))
                                            )
                                        };
                                        assert!(is_le(c));
                                        // then = Nil
                                        assert!(matches!(&t.content, PSymbol(s) if s == "Nil"));
                                        // else = Cons x (replicate (dec n) x)
                                        let is_cons_app = |p: &Program<RType>| {
                                            matches!(
                                                &p.content,
                                                PApp(f, _) if matches!(&f.content, PApp(s, _) if
                                                    matches!(&s.content, PSymbol(v) if v == "Cons"))
                                            )
                                        };
                                        assert!(is_cons_app(e));
                                        // The argument of replicate: (dec n) applied to x.
                                        let is_replicate_app = |p: &Program<RType>| {
                                            matches!(
                                                &p.content,
                                                PApp(f, x2) if
                                                    matches!(&f.content, PApp(s, _) if
                                                        matches!(&s.content, PSymbol(v) if v == "replicate")) &&
                                                    matches!(&x2.content, PSymbol(v) if v == "x")
                                            )
                                        };
                                        match &e.content {
                                            PApp(f, xs) => {
                                                assert!(is_replicate_app(xs));
                                                assert!(matches!(&f.content, PApp(s, _) if
                                                    matches!(&s.content, PSymbol(v) if v == "Cons")));
                                                match &xs.content {
                                                    PApp(f2, n2) => {
                                                        // f2 = replicate (dec n), n2 = x
                                                        assert!(
                                                            matches!(&f2.content, PApp(s, a1) if
                                                                matches!(&s.content, PSymbol(v) if v == "replicate") &&
                                                                matches!(&a1.content, PApp(d, n) if
                                                                    matches!(&d.content, PSymbol(v) if v == "dec") &&
                                                                    matches!(&n.content, PSymbol(v) if v == "n")))
                                                        );
                                                        assert!(
                                                            matches!(&n2.content, PSymbol(v) if v == "x")
                                                        );
                                                    }
                                                    _ => panic!("expected replicate application"),
                                                }
                                            }
                                            _ => panic!("expected something else"),
                                        }
                                    }
                                    _ => panic!("expected if"),
                                }
                            }
                            _ => panic!("expected second lambda"),
                        }
                    }
                    _ => panic!("expected first lambda"),
                }
            }
            _ => panic!("expected goal"),
        }
    }

    #[test]
    fn parses_delete_solution() {
        let decls = parse(DELETE_SOLUTION);
        assert_eq!(decls.len(), 7);
        let measure = &decls[2].node;
        match measure {
            BareDeclaration::MeasureDecl(name, in_sort, out_sort, post, cases, args, is_term) => {
                assert_eq!(name, "elems");
                assert_eq!(
                    in_sort,
                    &DataS("List".to_string(), vec![VarS("a".to_string())])
                );
                assert_eq!(out_sort, &SetS(Box::new(VarS("a".to_string()))));
                assert!(matches!(post, Formula::BoolLit(true)));
                assert_eq!(cases.len(), 2);
                assert_eq!(cases[0].constructor, "Nil");
                assert_eq!(cases[1].constructor, "Cons");
                assert!(args.is_empty());
                assert!(!is_term);
            }
            _ => panic!("expected measure"),
        }
        let delete = &decls[6].node;
        match delete {
            BareDeclaration::SynthesisGoal(name, body) => {
                assert_eq!(name, "delete");
                match &body.content {
                    PFun(x, b1) => {
                        assert_eq!(x, "x");
                        match &b1.content {
                            PFun(xs, b2) => {
                                assert_eq!(xs, "xs");
                                match &b2.content {
                                    PMatch(scr, cases) => {
                                        assert!(matches!(&scr.content, PSymbol(s) if s == "xs"));
                                        assert_eq!(cases.len(), 2);
                                        assert_eq!(cases[0].constructor, "Nil");
                                        assert_eq!(cases[0].arg_names.len(), 0);
                                        assert!(
                                            matches!(&cases[0].expr.content, PSymbol(s) if s == "xs")
                                        );
                                        assert_eq!(cases[1].constructor, "Cons");
                                        assert_eq!(cases[1].arg_names, vec!["x3", "x4"]);
                                        match &cases[1].expr.content {
                                            PIf(c, t, e) => {
                                                assert!(matches!(&c.content, PApp(_, _)));
                                                assert!(matches!(&t.content, PApp(_, _)));
                                                match &e.content {
                                                    PApp(..) => {}
                                                    _ => panic!("expected application"),
                                                }
                                            }
                                            _ => panic!("expected if"),
                                        }
                                    }
                                    _ => panic!("expected match"),
                                }
                            }
                            _ => panic!("expected second lambda"),
                        }
                    }
                    _ => panic!("expected first lambda"),
                }
            }
            _ => panic!("expected goal"),
        }
    }

    #[test]
    fn parses_type_shapes() {
        let decls = parse(
            "f :: List a -> Int\n\
             g :: x: Int -> {Int | _v > 0} -> {Int | _v >= x}\n\
             h :: [Int] -> Bool\n",
        );
        assert_eq!(decls.len(), 3);
        match &decls[0].node {
            BareDeclaration::FuncDecl(_, sch) => {
                match sch {
                    SchemaSkeleton::Monotype(TypeSkeleton::FunctionT(arg, a, b)) => {
                        // No named arg: "arg0".
                        assert_eq!(arg, "arg0");
                        assert!(matches!(
                            &**a,
                            TypeSkeleton::ScalarT(DatatypeT(name, args, _), _) if name == "List" && args.len() == 1
                        ));
                        assert!(matches!(&**b, TypeSkeleton::ScalarT(IntT, _)));
                    }
                    _ => panic!("expected monotype"),
                }
            }
            _ => panic!("expected func"),
        }
        match &decls[1].node {
            BareDeclaration::FuncDecl(_, sch) => match sch {
                SchemaSkeleton::Monotype(TypeSkeleton::FunctionT(arg, a, b)) => {
                    assert_eq!(arg, "x");
                    assert!(matches!(&**a, TypeSkeleton::ScalarT(IntT, _)));
                    match &**b {
                        TypeSkeleton::FunctionT(y, aa, bb) => {
                            assert_eq!(y, "arg0");
                            assert!(matches!(&**aa, TypeSkeleton::ScalarT(IntT, _)));
                            assert!(
                                matches!(&**bb, TypeSkeleton::ScalarT(IntT, f) if matches!(f, Formula::Binary(BinOp::Ge, _, _)))
                            );
                        }
                        _ => panic!("expected function type"),
                    }
                }
                _ => panic!("expected monotype"),
            },
            _ => panic!("expected func"),
        }
        match &decls[2].node {
            BareDeclaration::FuncDecl(_, sch) => match sch {
                SchemaSkeleton::Monotype(TypeSkeleton::FunctionT(arg, a, b)) => {
                    assert_eq!(arg, "arg0");
                    assert!(matches!(
                        &**a,
                        TypeSkeleton::ScalarT(DatatypeT(name, _, _), _) if name == "List"
                    ));
                    assert!(matches!(&**b, TypeSkeleton::ScalarT(BoolT, _)));
                }
                _ => panic!("expected monotype"),
            },
            _ => panic!("expected func"),
        }
    }

    #[test]
    fn parses_forall_and_set_ops() {
        let input = "\
elemIndex :: <p :: Int -> a -> Bool> . x: a -> xs: {List a <p> | x in elems _v} -> {Int | p _v x}
qualifier {x <= y, x != y}
";
        let decls = parse(input);
        assert_eq!(decls.len(), 2);
        match &decls[0].node {
            BareDeclaration::FuncDecl(_, sch) => match sch {
                SchemaSkeleton::ForallP(sig, _) => {
                    assert_eq!(sig.pred_sig_name, "p");
                    assert_eq!(sig.pred_sig_arg_sorts, vec![IntS, VarS("a".to_string())]);
                    assert_eq!(sig.pred_sig_res_sort, BoolS);
                }
                _ => panic!("expected forall"),
            },
            _ => panic!("expected func"),
        }
        match &decls[1].node {
            BareDeclaration::QualifierDecl(fs) => {
                assert_eq!(fs.len(), 2);
                assert!(matches!(&fs[0], Formula::Binary(BinOp::Le, _, _)));
                assert!(matches!(&fs[1], Formula::Binary(BinOp::Neq, _, _)));
            }
            _ => panic!("expected qualifier"),
        }
    }

    #[test]
    fn parses_precedence_and_associativity() {
        let decls = parse(
            "inline abs x = if x >= 0 then x else -x\n\
             inline f a b = 1 + 2 * 3\n\
             inline g a b = a ==> b ==> c\n\
             inline h a b = a <= b && c <= d\n\
             inline i a b = x in elems _v\n",
        );
        assert_eq!(decls.len(), 5);
        let inline = |i: usize| match &decls[i].node {
            BareDeclaration::InlineDecl(_, _, body) => body.clone(),
            _ => panic!("expected inline"),
        };
        // abs: if x >= 0 then x else -x
        match inline(0) {
            Formula::Ite(c, t, e) => {
                assert!(matches!(*c, Formula::Binary(BinOp::Ge, _, _)));
                assert!(matches!(*t, Formula::Var(_, v) if v == "x"));
                assert!(matches!(*e, Formula::Unary(UnOp::Neg, _)));
            }
            _ => panic!("expected ite"),
        }
        // 1 + 2 * 3
        match inline(1) {
            Formula::Binary(BinOp::Plus, l, r) => {
                assert!(matches!(*l, Formula::IntLit(1)));
                assert!(matches!(*r, Formula::Binary(BinOp::Times, _, _)));
            }
            _ => panic!("expected plus"),
        }
        // a ==> b ==> c is right-associative
        match inline(2) {
            Formula::Binary(BinOp::Implies, l, r) => {
                assert!(matches!(*l, Formula::Var(_, v) if v == "a"));
                assert!(matches!(*r, Formula::Binary(BinOp::Implies, _, _)));
            }
            _ => panic!("expected implies"),
        }
        // a <= b && c <= d
        match inline(3) {
            Formula::Binary(BinOp::And, l, r) => {
                assert!(matches!(*l, Formula::Binary(BinOp::Le, _, _)));
                assert!(matches!(*r, Formula::Binary(BinOp::Le, _, _)));
            }
            _ => panic!("expected and"),
        }
        // x in elems _v
        match inline(4) {
            Formula::Binary(BinOp::Member, l, r) => {
                assert!(matches!(*l, Formula::Var(_, v) if v == "x"));
                assert!(matches!(*r, Formula::Pred(_, p, args) if p == "elems" && args.len() == 1));
            }
            _ => panic!("expected member"),
        }
    }

    #[test]
    fn parses_match_and_annotations() {
        let input = "\
foo = \\x . let y = x in if x then (y :: Bool) else error
bar = match x with
        Nil -> [1, 2, 3]
        Cons a b -> (\\z . z) ??\n";
        let decls = parse(input);
        assert_eq!(decls.len(), 2);
        match &decls[0].node {
            BareDeclaration::SynthesisGoal(_, body) => {
                assert!(matches!(body.content, PFun(_, _)));
            }
            _ => panic!("expected goal"),
        }
        match &decls[1].node {
            BareDeclaration::SynthesisGoal(_, body) => match &body.content {
                PMatch(_, cases) => assert_eq!(cases.len(), 2),
                _ => panic!("expected match"),
            },
            _ => panic!("expected goal"),
        }
    }

    #[test]
    fn parses_data_with_pred_params() {
        let input = "\
data Foo a <p :: a -> Bool> ! where
\tA :: Foo a
data Bar a <p :: a -> a -> Bool> where
\tB :: Bar a\n";
        let decls = parse(input);
        match &decls[0].node {
            BareDeclaration::DataDecl(name, tvs, pps, cons) => {
                assert_eq!(name, "Foo");
                assert_eq!(tvs, &vec!["a".to_string()]);
                assert_eq!(pps.len(), 1);
                assert_eq!(pps[0].0.pred_sig_name, "p");
                assert!(pps[0].1);
                assert_eq!(cons.len(), 1);
            }
            _ => panic!("expected data"),
        }
        match &decls[1].node {
            BareDeclaration::DataDecl(_, _, pps, _) => {
                assert_eq!(pps.len(), 1);
                assert!(!pps[0].1);
                assert_eq!(pps[0].0.pred_sig_arg_sorts.len(), 2);
            }
            _ => panic!("expected data"),
        }
    }

    #[test]
    fn rejects_indentation_violations() {
        // Second declaration at a different column than the first.
        let bad = "f :: Int -> Int\n  g :: Int -> Int\n";
        let err = parse_err(bad);
        assert_eq!(err.kind, ErrorKind::ParseError);

        // Measure cases not indented past the reference column.
        let bad2 = "measure len :: List a -> Int where\nNil -> 0\n";
        let err2 = parse_err(bad2);
        assert_eq!(err2.kind, ErrorKind::ParseError);

        // Match cases at the same column as the match keyword.
        let bad3 = "foo = \\x . match x with\nNil -> x\n";
        let err3 = parse_err(bad3);
        assert_eq!(err3.kind, ErrorKind::ParseError);

        // Undeclared token.
        let bad4 = "@ not a valid token\n";
        assert_eq!(parse_err(bad4).kind, ErrorKind::ParseError);
    }

    #[test]
    fn parses_empty_input() {
        let decls = parse("");
        assert!(decls.is_empty());
        let decls2 = parse("   \n\n  -- comment only\n");
        assert!(decls2.is_empty());
    }

    #[test]
    fn parses_measure_with_constant_args() {
        let input = "\
termination measure count :: n: Int -> List a -> {Int | _v == n} where
  Nil -> n
  Cons x xs -> count (n + 1) xs\n";
        let decls = parse(input);
        match &decls[0].node {
            BareDeclaration::MeasureDecl(name, in_sort, out_sort, _, cases, args, is_term) => {
                assert_eq!(name, "count");
                assert_eq!(
                    in_sort,
                    &DataS("List".to_string(), vec![VarS("a".to_string())])
                );
                assert!(matches!(out_sort, Sort::IntS));
                assert_eq!(args, &vec![("n".to_string(), IntS)]);
                assert!(is_term);
                assert_eq!(cases.len(), 2);
                let c0 = &cases[0];
                assert!(c0.arg_names.is_empty());
                assert!(matches!(&c0.body, Formula::Var(_, v) if v == "n"));
            }
            _ => panic!("expected measure"),
        }
    }

    #[test]
    fn parses_sort_shapes() {
        let input = "\
f :: Int -> Bool -> Int -> Int
g :: List a -> List (a) -> Int\n";
        let decls = parse(input);
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn lexer_handles_comments_and_crlf() {
        let input = "{- block comment\r\nspanning lines -}\r\nf :: Int -> Int\r\n-- trailing comment\r\ng = 5\r\n";
        let decls = parse(input);
        assert_eq!(decls.len(), 2);
        match &decls[1].node {
            BareDeclaration::SynthesisGoal(_, body) => {
                assert!(matches!(&body.content, PSymbol(s) if s == "5"));
            }
            _ => panic!("expected goal"),
        }
    }
}
