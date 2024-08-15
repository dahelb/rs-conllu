//! A library for parsing the CoNNL-U format.
//!
//! ## Basic Usage
//!
//! Parse a sentence in CoNNL-U format and iterate over the
//! containing [`Token`] elements.
//! Example taken from [CoNLL-U format description](https://universaldependencies.org/format.html).
//!
//! ```
//! use rs_conllu::{parse_sentence, TokenID};
//!
//! let s = "# sent_id = 1
//! ## text = They buy and sell books.
//! 1	They	they	PRON	PRP	Case=Nom|Number=Plur	2	nsubj	2:nsubj|4:nsubj	_
//! 2	buy	buy	VERB	VBP	Number=Plur|Person=3|Tense=Pres	0	root	0:root	_
//! 3	and	and	CCONJ	CC	_	4	cc	4:cc	_
//! 4	sell	sell	VERB	VBP	Number=Plur|Person=4|Tense=Pres	2	conj	0:root|2:conj	_
//! 6	books	book	NOUN	NNS	Number=Plur	2	obj	2:obj|4:obj	SpaceAfter=No
//! 7	.	.	PUNCT	.	_	2	punct	2:punct	_
//! ";
//!
//! let sentence = parse_sentence(s).unwrap();
//! let mut token_iter = sentence.into_iter();
//!
//! assert_eq!(token_iter.next().unwrap().id, TokenID::Single(1));
//! assert_eq!(token_iter.next().unwrap().form, "buy".to_owned());
//!
//! ```

#![allow(clippy::tabs_in_doc_comments)]

use std::{error::Error, fmt, str::FromStr};

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
    pub meta: Vec<String>,
    pub tokens: Vec<Token>,
}

impl IntoIterator for Sentence {
    type Item = Token;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.tokens.into_iter()
    }
}
