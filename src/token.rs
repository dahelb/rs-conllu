use std::collections::HashMap;

use crate::UPOS;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum TokenID {
    /// The standard, single index.
    Single(usize),
    /// A range of tokens that form an ID. Denoted by a hyphen
    /// in CoNLL-U format (e.g. 1-3).
    Range(usize, usize),
    /// To represent ellipses, ConLL-U allows to create sub-indices of the preceding
    /// regular node (or 0 if it is a the beginning of a sentence). They are separated
    /// by a decimal point and represent an "empty" node.
    Empty(usize, usize),
}

type Features = HashMap<String, String>;

/// A `Token` is the basic unit of what is defined on a (non-comment) line in CoNLL-U format.
/// The ConLL-U specification uses the terms _word_, _node_ and _multi-word token_ while this crate
/// decided to use the general notion of _Token_ to subsume all of the above.
///
/// The fields of a `Token` are the ten fields that are defined in the CoNLL-U specification.
/// The only mandatory fields are [id](Token::id) and [form](Token::form). The remaining ones are optional (absence denoted
/// by an underscore in the text format) and represented as [Option] types.
///
/// A [TokenBuilder] type is available for more convenient creation of [Token] structs,
/// which can be instantiated via the [builder](Token::builder) method.
///
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Token {
    /// The id of the token within the sentence.
    pub id: TokenID,
    /// The surface form of the token as it appears in the sentence.
    pub form: String,
    /// The lemma or lexical form of the token.
    pub lemma: Option<String>,
    /// The universal POS tag of the token.
    pub upos: Option<UPOS>,
    /// Language-specific POS tag for the token.
    pub xpos: Option<String>,
    /// Morphological features of the token as key-value pairs.
    pub features: Option<Features>,
    /// The head of the current token.
    pub head: Option<TokenID>,
    /// The dependency relation fo the token.
    pub deprel: Option<String>,
    /// Enhanced dependency graph information.
    pub deps: Option<Vec<Dep>>,
    /// Other types of annotation.
    pub misc: Option<String>,
}

impl Token {
    /// Return a new [TokenBuilder].
    pub fn builder(id: TokenID, form: String) -> TokenBuilder {
        TokenBuilder::new(id, form)
    }
}

/// A builder for Tokens to allow for more convenient manual creation if necessary.
///
/// ```rust
/// use rs_conllu::{Token, TokenID};
///
/// // Get a new builder from Token
/// let token = Token::builder(TokenID::Single(1), "Hello".to_string())
///     .lemma("Hello".to_string())
///     .build();
///
/// ```
pub struct TokenBuilder {
    id: TokenID,
    form: String,
    lemma: Option<String>,
    upos: Option<UPOS>,
    xpos: Option<String>,
    features: Option<Features>,
    head: Option<TokenID>,
    deprel: Option<String>,
    deps: Option<Vec<Dep>>,
    misc: Option<String>,
}

impl TokenBuilder {
    /// Contstructor for [TokenBuilder]. Both `id` and `form` are mandatory
    /// fields and thus required when instantiating.
    pub fn new(id: TokenID, form: String) -> TokenBuilder {
        TokenBuilder {
            id,
            form,
            lemma: None,
            upos: None,
            xpos: None,
            features: None,
            head: None,
            deprel: None,
            deps: None,
            misc: None,
        }
    }

    /// Set the lemma field.
    pub fn lemma(mut self, lemma: String) -> TokenBuilder {
        self.lemma = Some(lemma);
        self
    }

    /// Set the universal POS tag field.
    pub fn upos(mut self, upos: UPOS) -> TokenBuilder {
        self.upos = Some(upos);
        self
    }

    /// Set the xpos field.
    pub fn xpos(mut self, xpos: String) -> TokenBuilder {
        self.xpos = Some(xpos);
        self
    }

    /// Set the features field.
    pub fn features(mut self, features: Features) -> TokenBuilder {
        self.features = Some(features);
        self
    }

    /// Set the head field.
    pub fn head(mut self, head: TokenID) -> TokenBuilder {
        self.head = Some(head);
        self
    }

    /// Set the deprel field.
    pub fn deprel(mut self, deprel: String) -> TokenBuilder {
        self.deprel = Some(deprel);
        self
    }

    /// Set the deps field.
    pub fn deps(mut self, dep: Vec<Dep>) -> TokenBuilder {
        self.deps = Some(dep);
        self
    }

    /// Set the misc field.
    pub fn misc(mut self, misc: String) -> TokenBuilder {
        self.misc = Some(misc);
        self
    }

    /// Build the token.
    pub fn build(self) -> Token {
        Token {
            id: self.id,
            form: self.form,
            lemma: self.lemma,
            upos: self.upos,
            xpos: self.xpos,
            features: self.features,
            head: self.head,
            deprel: self.deprel,
            deps: self.deps,
            misc: self.misc,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Dep {
    /// The head of the relation.
    pub head: TokenID,
    /// The type of the relation.
    pub rel: String,
}
