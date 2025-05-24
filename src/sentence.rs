//! Sentence and the related builder.

use std::collections::HashMap;

use crate::{Token, TokenID};

/// A single sentence, consists of [`Token`] elements and the associated
/// metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sentence {
    meta: Vec<String>,
    tokens: Vec<Token>,
    id_to_index: HashMap<TokenID, usize>,
}

impl Sentence {
    /// Return a new [`SentenceBuilder`]
    pub fn builder() -> SentenceBuilder {
        SentenceBuilder::default()
    }

    /// Get a reference of a [`Token`] by its id in the sentence.
    pub fn get_token(&self, id: TokenID) -> Option<&Token> {
        if let Some(idx) = self.id_to_index.get(&id) {
            let token = self.tokens.get(*idx);
            return token;
        }
        None
    }

    /// Get a mutable reference of a [`Token`] by its id in the sentence.
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

    /// Get the metdata of the sentence.
    pub fn get_meta(&self) -> &Vec<String> {
        &self.meta
    }

    /// Get an iterator over the [Token] elemens in the sentence.
    pub fn iter(&self) -> std::slice::Iter<Token> {
        self.tokens.iter()
    }

    /// Get an iterator over the [Token] elemens in the sentence.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<Token> {
        self.tokens.iter_mut()
    }
}

impl IntoIterator for Sentence {
    type Item = Token;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.tokens.into_iter()
    }
}

/// Builder for [`Sentence`] structs..
///
/// ```rust
/// use rs_conllu::{Sentence, Token, TokenID};
///
/// let t1 = Token::builder(TokenID::Single(1), "Hello".to_string()).build();
///
/// let sentence = Sentence::builder()
///     .with_meta(vec!["sent_id = 0".to_string()])
///     .push_token(t1)
///     .build();
/// ```
#[derive(Default)]
pub struct SentenceBuilder {
    tokens: Vec<Token>,
    meta: Vec<String>,
}

impl SentenceBuilder {
    /// Initialize the builder with a set of [`Token`] elements.
    pub fn with_tokens(mut self, tokens: Vec<Token>) -> SentenceBuilder {
        self.tokens = tokens;
        self
    }

    /// Set the metadata for the sentence.
    pub fn with_meta(mut self, meta: Vec<String>) -> SentenceBuilder {
        self.meta = meta;
        self
    }

    /// Add a single [`Token`] to the sentence being built.
    pub fn push_token(mut self, token: Token) -> SentenceBuilder {
        self.tokens.push(token);
        self
    }

    /// Consume the builder and create the final [`Sentence`] struct.
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
