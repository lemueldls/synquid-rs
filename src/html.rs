//! HTML rendering of rendered documents.
//!
//! The entry point `show_doc_html` converts an already-laid-out `SimpleDoc`
//! into the HTML fragment that the reference produces for `--output=Html`
//! (`renderHtmlNoHeader . docHtml`), byte for byte:
//!
//! - one `<DIV STYLE = "margin-left: Npx;">` per line, with `N = 7 * indent`;
//!   empty lines contain `&nbsp;`;
//! - SGR-colored spans become `<SPAN STYLE = "css">`; the SGR state is
//!   *replaced* at each escape boundary (a later escape does not accumulate
//!   onto an earlier one), and `Reset`-only states render plain text;
//! - text is HTML-escaped (`&`, `<`, `>`);
//! - the whole fragment ends with a trailing `"\n"` (the reference's `foldr (.)
//!   id ... "\n"`).

use crate::pretty::SimpleDoc;

/// Width in pixels of a single indentation position (`indentWidth`).
const INDENT_WIDTH: usize = 7;

/// Render a document into a string that contains the html code
/// (`showDocHtml`).
#[must_use]
pub fn show_doc_html(doc: &SimpleDoc) -> String {
    render_html_no_header(&doc_html(doc))
}

/// Render a document into an html object (`docHtml`).
fn doc_html(doc: &SimpleDoc) -> Vec<HtmlLine> {
    split_lines(doc)
}

/// A single rendered line: `(indent, spans)`, where each span is
/// `(css, text)` and plain text carries an empty css.
type HtmlLine = (usize, Vec<(String, String)>);

/// `splitLines sgrs indent currentLine next`: walk the `SimpleDoc`, cutting it
/// into one entry per line break. The SGR state carries across lines (an
/// escape at the start of a line with empty content emits nothing).
fn split_lines(doc: &SimpleDoc) -> Vec<HtmlLine> {
    let mut lines = Vec::new();
    let mut indent = 0usize;
    let mut sgr = String::new();
    let mut cur = String::new();
    let mut spans: Vec<(String, String)> = Vec::new();
    let mut rest = doc;
    loop {
        match rest {
            SimpleDoc::SEmpty => {
                push_span(&mut spans, &sgr, &mut cur);
                lines.push((indent, std::mem::take(&mut spans)));
                break;
            }
            SimpleDoc::SChar(c, next) => {
                cur.push(*c);
                rest = next;
            }
            SimpleDoc::SText(_, s, next) => {
                cur.push_str(s);
                rest = next;
            }
            SimpleDoc::SLine(i, next) => {
                push_span(&mut spans, &sgr, &mut cur);
                lines.push((indent, std::mem::take(&mut spans)));
                indent = *i;
                rest = next;
            }
            SimpleDoc::SSgr(s, next) => {
                push_span(&mut spans, &sgr, &mut cur);
                sgr.clone_from(s);
                rest = next;
            }
            SimpleDoc::SFail => {
                // Unreachable in practice: `best` panics on `DocNode::Fail`
                // before a `SimpleDoc` is produced.
                break;
            }
        }
    }
    lines
}

/// `genSpan sgrs currentSpan +++ splitStyles sgrs' id doc`: close the current
/// span (if non-empty), carrying the old SGR state.
fn push_span(spans: &mut Vec<(String, String)>, sgr: &str, cur: &mut String) {
    if cur.is_empty() {
        return;
    }
    let css = sgr_to_css(sgr);
    spans.push((css, std::mem::take(cur)));
}

/// `splitStyles sgrs currentSpan next`: convert one line's pieces into spans
/// (`genSpan`), mapping SGR codes to CSS.
fn sgr_to_css(sgr: &str) -> String {
    let codes = sgr
        .strip_prefix("\u{1b}[")
        .and_then(|r| r.strip_suffix('m'))
        .map(|c| c.split(';').collect::<Vec<_>>())
        .unwrap_or_default();
    if codes.is_empty() || codes == ["0"] {
        return String::new();
    }
    let mut css = String::new();
    for c in &codes {
        match *c {
            "1" => css.push_str("font-weight: bold;"),
            "22" => css.push_str("font-weight: normal;"),
            "3" => css.push_str("font-style: italic;"),
            "23" => css.push_str("font-style: normal;"),
            "4" => css.push_str("text-decoration: underline;"),
            "24" => css.push_str("text-decoration: none;"),
            _ => {}
        }
        if let Some((background, index)) = color_index(c) {
            let name = color_name(background, index);
            if background {
                css.push_str("background-color: ");
            } else {
                css.push_str("color: ");
            }
            css.push_str(name);
            css.push(';');
        }
    }
    css
}

/// Parse an SGR color code into `(background, color index)` per
/// `System.Console.ANSI`: 30-37/40-47 are dull foreground/background and
/// 90-97/100-107 are vivid.
fn color_index(code: &str) -> Option<(bool, usize)> {
    let (bg, base, digit) = match code.as_bytes() {
        [b'3', d] => (false, 30usize, *d),
        [b'4', d] => (true, 40usize, *d),
        [b'9', d] => (false, 90usize, *d),
        [b'1', b'0', d] => (true, 100usize, *d),
        _ => return None,
    };
    let digit = usize::from(digit - b'0');
    if digit > 7 {
        return None;
    }
    Some((bg, base + digit))
}

fn color_name(background: bool, code: usize) -> &'static str {
    let index = code % 10;
    let vivid = code >= 90;
    match (background, vivid, index) {
        (_, _, 0) => "Black",
        (_, true, 1) => "Red",
        (_, true, 2) => "Green",
        (_, true, 3) => "Yellow",
        (_, true, 4) => "Blue",
        (_, true, 5) => "Magenta",
        (_, true, 6) => "Cyan",
        (_, true, 7) => "White",
        (_, false, 1) => "DarkRed",
        (_, false, 2) => "DarkGreen",
        (_, false, 3) => "DarkKhaki",
        (_, false, 4) => "DarkBlue",
        (_, false, 5) => "DarkMagenta",
        (_, false, 6) => "DarkCyan",
        (_, false, 7) => "Gray",
        _ => unreachable!("color code out of range"),
    }
}

/// Generate HTML for a document that does not contain new lines or formatting
/// (`simple`), with HTML escaping (`&`, `<`, `>`).
fn escape_html(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            _ => out.push(c),
        }
    }
    out
}

/// Render a line into its `DIV` element (`genLine`).
fn render_div(line: &HtmlLine) -> String {
    let (indent, spans) = line;
    let mut out = format!(
        "<DIV STYLE = \"margin-left: {}px;\"\n>",
        indent * INDENT_WIDTH
    );
    if spans.is_empty() {
        out.push_str("&nbsp;");
    } else {
        for (css, text) in spans {
            let text = escape_html(text);
            if css.is_empty() {
                out.push_str(&text);
            } else {
                out.push_str(&format!("<SPAN STYLE = \"{css}\"\n  >{text}</SPAN\n  >"));
            }
        }
    }
    out.push_str("</DIV\n>");
    out
}

/// `renderHtmlNoHeader`: fold the rendered elements, appending a single
/// trailing newline.
fn render_html_no_header(lines: &[HtmlLine]) -> String {
    let mut out = String::new();
    for line in lines {
        out.push_str(&render_div(line));
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty::{
        color, empty, intensify, plain, render_pretty, text, Color, ColorIntensity,
        ConsoleIntensity, ConsoleLayer,
    };

    fn html(d: &crate::pretty::Doc) -> String {
        show_doc_html(&render_pretty(0.4, 100, d))
    }

    #[test]
    fn empty_doc_is_nbsp_div() {
        assert_eq!(
            html(&empty()),
            "<DIV STYLE = \"margin-left: 0px;\"\n>&nbsp;</DIV\n>\n"
        );
    }

    #[test]
    fn plain_text_is_escaped() {
        let d = text("a < b && c > d");
        assert_eq!(
            html(&d),
            "<DIV STYLE = \"margin-left: 0px;\"\n>a &lt; b &amp;&amp; c &gt; d</DIV\n>\n"
        );
    }

    #[test]
    fn indent_scales_with_line_indent() {
        let d = crate::pretty::nest(
            2,
            crate::pretty::hcat(vec![crate::pretty::linebreak(), text("x")]),
        );
        let s = html(&d);
        assert!(s.starts_with(
            "<DIV STYLE = \"margin-left: 0px;\"\n>&nbsp;</DIV\n><DIV STYLE = \"margin-left: 14px;\"\n>x"
        ));
    }

    #[test]
    fn colored_text_becomes_span() {
        let d = color(
            ConsoleLayer::Foreground,
            ColorIntensity::Dull,
            Color::White,
            text("::"),
        );
        assert_eq!(
            html(&d),
            "<DIV STYLE = \"margin-left: 0px;\"\n><SPAN STYLE = \"color: Gray;\"\n  >::</SPAN\n  ></DIV\n>\n"
        );
    }

    #[test]
    fn vivid_white_is_while() {
        let d = color(
            ConsoleLayer::Foreground,
            ColorIntensity::Vivid,
            Color::White,
            text("w"),
        );
        assert!(html(&d).contains("color: While;"));
    }

    #[test]
    fn bold_becomes_font_weight() {
        let d = intensify(ConsoleIntensity::Bold, text("v"));
        assert!(html(&d).contains("font-weight: bold;"));
    }

    #[test]
    fn reset_only_renders_plain() {
        let d = color(
            ConsoleLayer::Foreground,
            ColorIntensity::Vivid,
            Color::Red,
            text("x"),
        );
        let s = html(&d);
        assert!(s.contains("color: Red;"));
        assert!(s.ends_with("x</SPAN\n  ></DIV\n>\n"));
        let d = plain(&d);
        assert_eq!(html(&d), "<DIV STYLE = \"margin-left: 0px;\"\n>x</DIV\n>\n");
    }

    #[test]
    fn multiple_lines_get_divs_without_separators() {
        let d = crate::pretty::nest(
            1,
            crate::pretty::hcat(vec![text("a"), crate::pretty::linebreak(), text("b")]),
        );
        assert_eq!(
            html(&d),
            "<DIV STYLE = \"margin-left: 0px;\"\n>a</DIV\n><DIV STYLE = \"margin-left: 7px;\"\n>b</DIV\n>\n"
        );
    }
}
