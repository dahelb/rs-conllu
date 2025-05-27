//! Parsers for tokens, sentences and whole documents, and associated code.

use std::{collections::HashMap, fs::File, io::Read, num::ParseIntError, str::FromStr, vec};
use thiserror::Error;

use crate::{
    sentence::Sentence,
    token::{Dep, Token, TokenID},
    ParseUposError, UPOS,
};

/// Errors resulting from parsing a token id.
#[derive(Error, PartialEq, Debug, Eq)]
pub enum ParseIdError {
    /// The id range could not be parsed.
    #[error("Range must be two integers separated by -")]
    InvalidRange,
    /// The id could not be parsed as an integer.
    #[error("Could not parse {input:?} as integer.")]
    FailedIntParsing {
        /// The input that failed to parse.
        input: String,
        /// The source error.
        source: ParseIntError,
    },
}

/// Error resulting from parsing a [`Token`].
#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseErrorType {
    /// An expected fiel is missing.
    #[error("Missing field: {0}")]
    MissingField(&'static str),
    /// The id failed to parse.
    #[error(transparent)]
    FailedIdParse(#[from] ParseIdError),
    /// Error in parsing the UPOS tag.
    #[error("Failed to parse field {field} as UPOS")]
    FailedUposParse {
        /// The source error.
        source: ParseUposError,
        /// The field that was tried to be parsed.
        field: String,
    },
    /// Error in parsing a field that consists of key-value pairs
    /// separated by a `=`
    #[error("Key value pairs must be separated by `=`")]
    KeyValueParseError,
}

/// Error when parsing a file in CoNLL-U format.
#[derive(Error, Debug, PartialEq, Eq)]
#[error("Parse error in line {line}: {err}")]
pub struct ConlluParseError {
    line: usize,
    err: ParseErrorType,
}

/// Parse a file into a [`ParsedDoc`].
///
///
/// ```rust
/// use std::fs::File;
///
/// # use std::error::Error;
/// use rs_conllu::parse_file;
///
/// # fn main() -> Result<(), Box<dyn Error>> {
/// let file = File::open("tests/example.conllu")?;
/// # Ok(())
/// # }
/// ```
pub fn parse_file(file: File) -> Result<ParsedDoc, ConlluParseError> {
    Parser::new(file).parse()
}

/// Parse a single line in CoNLL-U format into a [`Token`].
/// ```
/// use rs_conllu::{Token, TokenID, UPOS, parse_token};
///
/// let line = "6	Rust	Rust	NOUN	NN	_	3	nmod	_	_";
///
/// assert_eq!(parse_token(line).unwrap(), Token {
///     id: TokenID::Single(6),
///     form: "Rust".to_string(),
///     lemma: Some("Rust".to_string()),
///     upos: Some(UPOS::NOUN),
///     xpos: Some("NN".to_string()),
///     features: None,
///     head: Some(TokenID::Single(3)),
///     deprel: Some("nmod".to_string()),
///     deps: None,
///     misc: None
/// });
/// ```
pub fn parse_token(line: &str) -> Result<Token, ParseErrorType> {
    let mut fields_iter = line.split('\t');

    let id = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("id"))?;
    let id = parse_id(id)?;

    let form = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("form"))?;
    let form = String::from(form);

    let lemma = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("lemma"))?;
    let lemma = placeholder(lemma).map(String::from);

    let upos = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("upos"))?;
    let upos = placeholder_result(upos, str::parse::<UPOS>)
        .transpose()
        .map_err(|e| ParseErrorType::FailedUposParse {
            source: e,
            field: upos.to_string(),
        })?;

    let xpos = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("xpos"))?;
    let xpos = placeholder(xpos).map(String::from);

    let features = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("features"))?;
    let features = placeholder_result(features, parse_key_value_pairs).transpose()?;

    let head = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("head"))?;
    let head = placeholder_result(head, parse_id).transpose()?;

    let deprel = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("deprel"))?;
    let deprel = placeholder(deprel).map(String::from);

    let deps = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("deps"))?;
    let deps = placeholder_result(deps, parse_deps).transpose()?;

    let misc = fields_iter
        .next()
        .ok_or(ParseErrorType::MissingField("misc"))?;
    let misc = placeholder(misc).map(String::from);

    Ok(Token {
        id,
        form,
        lemma,
        upos,
        xpos,
        features,
        head,
        deprel,
        deps,
        misc,
    })
}

fn parse_int(input: &str) -> Result<usize, ParseIdError> {
    let parsed = usize::from_str(input).map_err(|e| ParseIdError::FailedIntParsing {
        input: input.to_string(),
        source: e,
    })?;
    Ok(parsed)
}

fn parse_id(field: &str) -> Result<TokenID, ParseIdError> {
    let sep = ['-', '.'].iter().find(|s| field.contains(**s));

    if let Some(sep) = sep {
        let ids: Vec<&str> = field.split(*sep).collect();

        let ids = ids
            .iter()
            .map(|s| parse_int(s))
            .collect::<Result<Vec<usize>, _>>();

        let ids = ids?;

        if ids.len() != 2 {
            return Err(ParseIdError::InvalidRange);
        }

        return match sep {
            '-' => Ok(TokenID::Range(ids[0], ids[1])),
            '.' => Ok(TokenID::Empty(ids[0], ids[1])),
            _ => unreachable!("Separator was checked to be only '-' or '.'"),
        };
    }

    Ok(TokenID::Single(parse_int(field)?))
}

fn parse_key_value_pairs(field: &str) -> Result<HashMap<String, String>, ParseErrorType> {
    let kv_pairs: Vec<&str> = field.split('|').collect();
    let features: Result<Vec<(&str, &str)>, _> = kv_pairs
        .iter()
        .map(|p| p.split_once('=').ok_or(ParseErrorType::KeyValueParseError))
        .collect();

    let features: HashMap<String, String> = features?
        .iter()
        .map(|t| (t.0.to_owned(), t.1.to_owned()))
        .collect();

    Ok(features)
}

fn parse_deps(field: &str) -> Result<Vec<Dep>, ParseErrorType> {
    let kv_pairs: Vec<&str> = field.split('|').collect();
    let deps: Result<Vec<(&str, &str)>, _> = kv_pairs
        .iter()
        .map(|p| p.split_once(':').ok_or(ParseErrorType::KeyValueParseError))
        .collect();

    let deps: Result<Vec<Dep>, ParseIdError> = deps?
        .iter()
        .map(|t| {
            Ok(Dep {
                head: parse_id(t.0)?,
                rel: String::from(t.1),
            })
        })
        .collect();

    Ok(deps?)
}

fn placeholder(field: &str) -> Option<&str> {
    match field {
        "_" => None,
        _ => Some(field),
    }
}

fn placeholder_result<O, F>(field: &str, f: F) -> Option<O>
where
    F: FnOnce(&str) -> O,
{
    match field {
        "_" => None,
        _ => Some(f(field)),
    }
}

/// Parses a single sentence in ConLL-U format.
pub fn parse_sentence(input: &str) -> Result<Sentence, ConlluParseError> {
    let mut meta = vec![];
    let mut tokens = vec![];
    for (i, line) in input.lines().enumerate() {
        if let Some(comment) = line.strip_prefix('#') {
            let comment = comment.trim_start();
            meta.push(comment.to_string());
            continue;
        }
        if !line.is_empty() {
            let token = parse_token(line).map_err(|e| ConlluParseError { err: e, line: i })?;
            tokens.push(token);
        }
    }
    Ok(Sentence::builder()
        .with_tokens(tokens)
        .with_meta(meta)
        .build())
}

/// A `Parser` is a wrapper around a type that implements [Read] and produces
/// lines in ConLL-U format that can be parsed into sentences, which in turn
/// can be accessed via iteration.
///
///
/// ```rust
/// use rs_conllu::{Sentence, Token, TokenID};
/// use rs_conllu::parsers::Parser;
///
/// let conllu = "1\tSue\t_\t_\t_\t_\t_\t_\t_\t_
/// 2\tlikes\t_\t_\t_\t_\t_\t_\t_\t_
/// 3\tcoffee\t_\t_\t_\t_\t_\t_\t_\t_
/// ".as_bytes();
///
/// let parsed = Parser::new(conllu).parse().unwrap();
///
/// assert_eq!(parsed.into_iter().next(), Some(
///     Sentence::builder().with_tokens(
///         vec![
///             Token::builder(TokenID::Single(1), "Sue".to_string()).build(),
///             Token::builder(TokenID::Single(2), "likes".to_string()).build(),
///             Token::builder(TokenID::Single(3), "coffee".to_string()).build(),
///         ],
///     ).build()
/// ));
/// ```
/// For the common use case of parsing a file in CoNLL-U format,
/// this crate provides the convenience function [parse_file] for parsing a file into
/// a [`ParsedDoc`].
///
pub struct Parser<T: Read> {
    reader: T,
}

impl<T: Read> Parser<T> {
    /// Create a new parser.
    pub fn new(reader: T) -> Self {
        Parser { reader }
    }

    /// Parse the whole document.
    pub fn parse(mut self) -> Result<ParsedDoc, ConlluParseError> {
        let mut buffer = String::new();
        self.reader.read_to_string(&mut buffer).unwrap();

        let sentence_splitter = SentenceSplitter::new(&buffer);
        let sentences: Result<Vec<_>, _> = sentence_splitter.map(parse_sentence).collect();

        let sentences = sentences?;

        Ok(ParsedDoc { sentences })
    }
}

struct SentenceSplitter<'a> {
    remaining: &'a str,
    finished: bool,
}

impl<'a> SentenceSplitter<'a> {
    fn new(s: &'a str) -> Self {
        SentenceSplitter {
            remaining: s,
            finished: false,
        }
    }
}

impl<'a> Iterator for SentenceSplitter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished || self.remaining.is_empty() {
            return None;
        }
        let maybe_sentence = self.remaining.split_once("\n\n");

        if let Some((sentence, remainder)) = maybe_sentence {
            self.remaining = remainder;
            Some(sentence)
        } else {
            self.finished = true;
            Some(self.remaining)
        }
    }
}

/// Represents a collection of parsed [`Sentence`] elements.
pub struct ParsedDoc {
    sentences: Vec<Sentence>,
}

impl ParsedDoc {
    /// Iterate over the containing [`Sentence`] elements.
    pub fn iter(&self) -> std::slice::Iter<Sentence> {
        self.sentences.iter()
    }

    /// Iterate __mutably__ over the containing [`Sentence`] elements.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<Sentence> {
        self.sentences.iter_mut()
    }
}

impl IntoIterator for ParsedDoc {
    type Item = Sentence;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.sentences.into_iter()
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{Token, UPOS};

    use super::*;

    #[test]
    fn can_parse_single_id() {
        assert_eq!(parse_id("5"), Ok(TokenID::Single(5)));
    }

    #[test]
    fn can_parse_id_range() {
        assert_eq!(parse_id("5-6"), Ok(TokenID::Range(5, 6)));
    }

    #[test]
    fn can_parse_id_empty() {
        assert_eq!(parse_id("5.6"), Ok(TokenID::Empty(5, 6)));
    }

    #[test]
    fn test_token_parse() {
        let line =
            "2	Ein	ein	DET	DT	Case=Nom|Definite=Ind|Gender=Masc|Number=Sing|Person=3	3	det	_	_";

        let features = HashMap::from([
            ("Case".to_string(), "Nom".to_string()),
            ("Definite".to_string(), "Ind".to_string()),
            ("Gender".to_string(), "Masc".to_string()),
            ("Number".to_string(), "Sing".to_string()),
            ("Person".to_string(), "3".to_string()),
        ]);

        let token = Token {
            id: TokenID::Single(2),
            form: "Ein".to_string(),
            lemma: Some("ein".to_string()),
            upos: Some(UPOS::DET),
            xpos: Some("DT".to_string()),
            features: Some(features),
            head: Some(TokenID::Single(3)),
            deprel: Some("det".to_string()),
            deps: None,
            misc: None,
        };

        assert_eq!(token, parse_token(line).unwrap());
    }

    #[test]
    fn test_sentence_split() {
        let s = "foo\nbar\n\nfoo\nbaz";

        let mut splitter = SentenceSplitter::new(s);

        assert_eq!(splitter.next(), Some("foo\nbar"));
        assert_eq!(splitter.next(), Some("foo\nbaz"));
        assert!(splitter.next().is_none());
    }

    #[test]
    fn test_sentence_split_trailing_newline() {
        let s = "foo\nbar\n\nfoo\nbaz\n";

        let mut splitter = SentenceSplitter::new(s);

        assert_eq!(splitter.next(), Some("foo\nbar"));
        assert_eq!(splitter.next(), Some("foo\nbaz\n"));
        assert!(splitter.next().is_none());
    }
}
