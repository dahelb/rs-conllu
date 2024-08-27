use std::{
    collections::HashMap,
    fs::File,
    io::{BufRead, BufReader},
    num::ParseIntError,
    str::FromStr,
    vec,
};
use thiserror::Error;

use crate::{
    token::{Dep, Token, TokenID},
    ParseUposError, Sentence, UPOS,
};

#[derive(Error, PartialEq, Debug, Eq)]
pub enum ParseIdError {
    #[error("Range must be two integers separated by -")]
    InvalidRange,
    #[error("Could not parse {input:?} as integer.")]
    FailedIntParsing {
        input: String,
        source: ParseIntError,
    },
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseErrorType {
    #[error("Missing field: {0}")]
    MissingField(&'static str),
    #[error(transparent)]
    FailedIdParse(#[from] ParseIdError),
    #[error("Failed to parse field {field} as UPOS")]
    FailedUposParse {
        source: ParseUposError,
        field: String,
    },
    #[error("Key value pairs must be separated by `=`")]
    KeyValueParseError,
}

#[derive(Error, Debug, PartialEq, Eq)]
#[error("Parse error in line {line}: {err}")]
pub struct ConlluParseError {
    line: usize,
    err: ParseErrorType,
}

impl ConlluParseError {
    fn adjust_line(&mut self, offset: usize) {
        self.line += offset
    }
}

pub fn parse_file(file: File) -> Doc<BufReader<File>> {
    let reader = BufReader::new(file);

    Doc::new(reader)
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
            _ => panic!(),
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

/// A `Doc` is a wrapper around a type that implements [BufRead] and produces
/// lines in ConLL-U format that can be parsed into sentences, which
/// can be accessed via iteration.
///
///  For the common use case of parsing a file in CoNLL-U format,
///  this crate provides the convenience function [parse_file], which produces a `Doc<BufReader<File>>`.
///
/// ```rust
/// use std::io::BufReader;
/// use rs_conllu::{Sentence, Token, TokenID};
/// use rs_conllu::parsers::Doc;
///
/// let conllu = "1\tSue\t_\t_\t_\t_\t_\t_\t_\t_
/// 2\tlikes\t_\t_\t_\t_\t_\t_\t_\t_
/// 3\tcoffee\t_\t_\t_\t_\t_\t_\t_\t_
/// ".as_bytes();
///
/// let reader = BufReader::new(conllu);
///
/// let mut doc = Doc::new(reader);
///
/// assert_eq!(doc.next(), Some(Ok(
///     Sentence::builder().with_tokens(
///         vec![
///             Token::builder(TokenID::Single(1), "Sue".to_string()).build(),
///             Token::builder(TokenID::Single(2), "likes".to_string()).build(),
///             Token::builder(TokenID::Single(3), "coffee".to_string()).build(),
///         ],
///     ).build()
/// )));
/// ```
pub struct Doc<T: BufRead> {
    reader: T,
    line_num: usize,
}

impl<T: BufRead> Doc<T> {
    pub fn new(reader: T) -> Self {
        Doc {
            reader,
            line_num: 0,
        }
    }
}

impl<T: BufRead> Iterator for Doc<T> {
    type Item = Result<Sentence, ConlluParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut buffer = String::new();
        let mut num_lines_in_buffer = 0;

        // try to read a line from the buffer
        // if we read 0 bytes, we are at EOF and stop the iteration
        // by returning None
        let mut bytes = self.reader.read_line(&mut buffer).unwrap();
        self.line_num += 1;
        num_lines_in_buffer += 1;
        if bytes == 0 {
            return None;
        }

        // fill the buffer until we are at a sentence break
        // or at the end of the file
        // while !buffer.ends_with("\n\n") && bytes != 0 {
        //     bytes = self.reader.read_line(&mut buffer).unwrap();
        // }
        loop {
            bytes = self.reader.read_line(&mut buffer).unwrap();
            self.line_num += 1;
            num_lines_in_buffer += 1;
            if buffer.ends_with("\n\n") {
                break;
            }
            // at EOF, the buffer terminates with a single newline.
            // To treat them equally with other sentences finishing in
            // a double newline, add one here.
            if bytes == 0 {
                buffer.push('\n');
                break;
            }
        }
        Some(parse_sentence(&buffer).map_err(|mut e| {
            e.adjust_line(self.line_num - num_lines_in_buffer + 1);
            e
        }))
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
}
