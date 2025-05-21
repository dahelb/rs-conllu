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
//! let parsed = parse_file(file)?;
//!
//! // parse_file returns a `ParsedDoc`, which allows iteration
//! // over the contained sentences.
//! for sentence in parsed {
//!     // we can also iterate over the contained sentences
//!     for token in sentence {
//!         // Process token, e.g. access individual fields.
//!         println!("{}", token.form)
//!     }
//! }
//! # Ok(())
//! # }
//!
//! ```
//! ## Modifying
//!
//! If manipulation is necessary, sentences can be iterated
//! mutably. The example below shows how we can change the
//! `form` and `lemma` of a particular token.
//!
//!
//! ```
//! use rs_conllu::{parse_file, Sentence, TokenID};
//! use std::fs::File;
//!
//! # use std::error::Error;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let file = File::open("tests/example.conllu")?;
//!
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

#![allow(clippy::tabs_in_doc_comments)]

use std::{error::Error, fmt, str::FromStr};

pub mod parsers;
pub mod sentence;
pub mod token;

pub use sentence::Sentence;
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
