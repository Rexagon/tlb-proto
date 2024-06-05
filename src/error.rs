use std::collections::BTreeSet;

use chumsky::util::MaybeRef;
use miette::SourceSpan;

#[derive(Debug, miette::Diagnostic, thiserror::Error)]
#[error("error parsing TLB")]
pub struct Error {
    #[related]
    pub(crate) errors: Vec<miette::Report>,
}

#[derive(Debug, miette::Diagnostic, thiserror::Error)]
pub enum ResolverError {
    #[error("{message}")]
    Unexpected {
        #[label("unexpected {kind}")]
        span: SourceSpan,
        kind: &'static str,
        message: String,
    },
}

#[derive(Debug, miette::Diagnostic, thiserror::Error)]
pub enum ParserError {
    #[error("{}", FormatUnexpected(found, expected))]
    #[diagnostic()]
    Unexpected {
        label: Option<&'static str>,
        #[label("{}", label.unwrap_or("unexpected token"))]
        span: SourceSpan,
        found: TokenFormat,
        expected: BTreeSet<TokenFormat>,
    },
    #[error("unclosed {label} {opened}")]
    #[diagnostic()]
    Unclosed {
        label: &'static str,
        #[label = "opened here"]
        opened_at: SourceSpan,
        opened: TokenFormat,
        #[label("expected {expected}")]
        expected_at: SourceSpan,
        expected: TokenFormat,
        found: TokenFormat,
    },
    #[error("{message}")]
    #[diagnostic()]
    Message {
        label: Option<&'static str>,
        #[label("{}", label.unwrap_or("unexpected token"))]
        span: SourceSpan,
        message: String,
    },
    #[error("{message}")]
    #[diagnostic(help("{help}"))]
    MessageWithHelp {
        label: Option<&'static str>,
        #[label("{}", label.unwrap_or("unexpected token"))]
        span: SourceSpan,
        message: String,
        help: &'static str,
    },
}

impl ParserError {
    pub(crate) fn with_expected_token(mut self, token: &'static str) -> Self {
        if let Self::Unexpected { expected, .. } = &mut self {
            *expected = BTreeSet::from([TokenFormat::Token(token)]);
        }
        self
    }

    pub(crate) fn with_expected_kind(mut self, token: &'static str) -> Self {
        if let Self::Unexpected { expected, .. } = &mut self {
            *expected = [TokenFormat::Kind(token)].into_iter().collect();
        }
        self
    }

    pub(crate) fn with_no_expected(mut self) -> Self {
        if let Self::Unexpected { expected, .. } = &mut self {
            *expected = BTreeSet::new();
        }
        self
    }
}

#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum TokenFormat {
    Char(char),
    Token(&'static str),
    Kind(&'static str),
    Eoi,
}

impl From<Option<MaybeRef<'_, char>>> for TokenFormat {
    fn from(chr: Option<MaybeRef<'_, char>>) -> TokenFormat {
        if let Some(chr) = chr {
            TokenFormat::Char(*chr)
        } else {
            TokenFormat::Eoi
        }
    }
}

impl From<char> for TokenFormat {
    fn from(chr: char) -> TokenFormat {
        TokenFormat::Char(chr)
    }
}

impl From<&'static str> for TokenFormat {
    fn from(s: &'static str) -> TokenFormat {
        TokenFormat::Token(s)
    }
}

impl std::fmt::Display for TokenFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use TokenFormat::*;
        match self {
            Char('"') => write!(f, "`\"`"),
            Char('\'') => write!(f, "`\'`"),
            Char('\\') => write!(f, r"`\`"),
            Char(c) => write!(f, "`{}`", c.escape_default()),
            Token(s) => write!(f, "`{}`", s.escape_default()),
            Kind(s) => write!(f, "{}", s),
            Eoi => write!(f, "end of input"),
        }
    }
}

struct FormatUnexpected<'x>(&'x TokenFormat, &'x BTreeSet<TokenFormat>);

impl std::fmt::Display for FormatUnexpected<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "found {}", self.0)?;
        let mut iter = self.1.iter();
        if let Some(item) = iter.next() {
            write!(f, ", expected {}", item)?;
            let back = iter.next_back();
            for item in iter {
                write!(f, ", {}", item)?;
            }
            if let Some(item) = back {
                write!(f, " or {}", item)?;
            }
        }
        Ok(())
    }
}

pub(crate) fn map_span(span: crate::parser::Span) -> SourceSpan {
    SourceSpan::new(span.start.into(), span.end.saturating_sub(span.start))
}
