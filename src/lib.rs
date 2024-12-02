//! A library for parsing the CoNNL-U format.
//!
//! ## Basic Usage
//!
//! ```
//! use rs_conllu::parse_file;
//! use std::fs::File;
//!
//! # use std::error::Error;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let file = File::open("tests/example.conllu")?;
//!
//! // Doc is an iterator over the containing sentences.
//! let parsed = parse_file(file)?;
//!
//! for sentence in parsed {
//!     for token in sentence {
//!         // Process token, e.g. access individual fields.
//!         println!("{}", token.form)
//!     }
//! }
//! # Ok(())
//! # }
//!
//! ```
//! ## Using Iterator Patterns
//!
//! ```
//! use rs_conllu::{parse_file, Sentence, TokenID};
//! use std::fs::File;
//!
//! # use std::error::Error;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let file = File::open("tests/example.conllu")?;
//!
//! // Doc is an iterator over the containing sentences.
//! let mut parsed = parse_file(file)?;
//!
//! if let Some(s) = parsed.iter_mut().nth(0) {
//!     if let Some(token) = s.get_token_mut(TokenID::Single(6)) {
//!         token.form = "crabs".to_string();
//!         token.lemma = Some("crab".to_string());
//!     }
//! }
//!
//! # Ok(())
//! # }
//! ```
//!

#![allow(clippy::tabs_in_doc_comments)]

use std::{collections::HashMap, error::Error, fmt, str::FromStr};

pub mod parsers;
pub mod token;

pub use token::{Dep, Token, TokenID};

pub use parsers::{parse_file, parse_sentence, parse_token};

#[cfg(feature = "serde")]
pub use serde::{Deserialize, Serialize};

pub struct Feature<'a>(pub &'a str, pub &'a str);

#[derive(Debug, PartialEq, Eq)]
pub struct ParseUposError;

impl fmt::Display for ParseUposError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error while parsing UPOS.")
    }
}

impl Error for ParseUposError {}

/// The set of Universal POS tags according
/// to [UD version 2](https://universaldependencies.org/u/pos/index.html).
#[derive(Debug, Clone, Copy, PartialEq, Eq, derive_more::Display)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum UPOS {
    ADJ,
    ADP,
    ADV,
    AUX,
    CCONJ,
    DET,
    INTJ,
    NOUN,
    NUM,
    PART,
    PRON,
    PROPN,
    PUNCT,
    SCONJ,
    SYM,
    VERB,
    X,
}

impl FromStr for UPOS {
    type Err = ParseUposError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        use UPOS::*;
        match value {
            "ADJ" => Ok(ADJ),
            "ADP" => Ok(ADP),
            "ADV" => Ok(ADV),
            "AUX" => Ok(AUX),
            "CCONJ" => Ok(CCONJ),
            "DET" => Ok(DET),
            "INTJ" => Ok(INTJ),
            "NOUN" => Ok(NOUN),
            "NUM" => Ok(NUM),
            "PART" => Ok(PART),
            "PRON" => Ok(PRON),
            "PROPN" => Ok(PROPN),
            "PUNCT" => Ok(PUNCT),
            "SCONJ" => Ok(SCONJ),
            "SYM" => Ok(SYM),
            "VERB" => Ok(VERB),
            "X" => Ok(X),
            _ => Err(ParseUposError),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Sentence {
    meta: Vec<String>,
    tokens: Vec<Token>,
    id_to_index: HashMap<TokenID, usize>,
}

impl Sentence {
    pub fn builder() -> SentenceBuilder {
        SentenceBuilder::default()
    }

    pub fn get_token(&self, id: TokenID) -> Option<&Token> {
        if let Some(idx) = self.id_to_index.get(&id) {
            let token = self.tokens.get(*idx);
            return token;
        }
        None
    }

    /// Get a mutable reference of a Token by its id in the sentence.
    ///
    /// ```rust
    /// use rs_conllu::{TokenID, parse_sentence};
    ///
    /// let mut sentence = parse_sentence("
    /// 1\tHello\thello\t_\t_\t_\t_\t_\t_\t_
    /// ").unwrap();
    ///
    /// let mut token = sentence.get_token_mut(TokenID::Single(1)).unwrap();
    /// ```
    pub fn get_token_mut(&mut self, id: TokenID) -> Option<&mut Token> {
        if let Some(idx) = self.id_to_index.get(&id) {
            let token = self.tokens.get_mut(*idx);
            return token;
        }
        None
    }

    pub fn get_meta(&self) -> &Vec<String> {
        &self.meta
    }

    /// Get an iterator over the [Token] elemens in the sentence.
    pub fn token_iter(&self) -> impl Iterator<Item = &Token> {
        self.tokens.iter()
    }
}

impl IntoIterator for Sentence {
    type Item = Token;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.tokens.into_iter()
    }
}

#[derive(Default)]
pub struct SentenceBuilder {
    tokens: Vec<Token>,
    meta: Vec<String>,
}

impl SentenceBuilder {
    pub fn with_tokens(mut self, tokens: Vec<Token>) -> SentenceBuilder {
        self.tokens = tokens;
        self
    }

    pub fn with_meta(mut self, meta: Vec<String>) -> SentenceBuilder {
        self.meta = meta;
        self
    }

    pub fn push_token(mut self, token: Token) -> SentenceBuilder {
        self.tokens.push(token);
        self
    }

    pub fn build(self) -> Sentence {
        let id_to_index: HashMap<TokenID, usize> = self
            .tokens
            .iter()
            .map(|t| t.id)
            .enumerate()
            .map(|(i, token)| (token, i))
            .collect();

        Sentence {
            meta: self.meta,
            tokens: self.tokens,
            id_to_index,
        }
    }
}
