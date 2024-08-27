use std::collections::HashMap;

use crate::token::{Token, TokenID};

#[derive(Debug, Clone, PartialEq, Eq)]
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
