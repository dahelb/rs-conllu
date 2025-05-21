use std::{collections::HashMap, fs::File};

use rs_conllu::{
    parse_file,
    token::{Dep, Token, TokenID},
    UPOS,
};

#[test]
fn test_file_parse() {
    let file = File::open("./tests/example.conllu").unwrap();

    let s = parse_file(file).unwrap().into_iter().next().unwrap();

    let mut token_iter = s.into_iter();

    let token = token_iter.next().unwrap();

    assert_eq!(
        token,
        Token {
            id: TokenID::Single(1),
            form: "They".to_string(),
            lemma: Some("they".to_string()),
            upos: Some(UPOS::PRON),
            xpos: Some("PRP".to_string()),
            features: Some(HashMap::from([
                ("Case".to_string(), "Nom".to_string()),
                ("Number".to_string(), "Plur".to_string())
            ])),
            head: Some(TokenID::Single(2)),
            deprel: Some("nsubj".to_string()),
            deps: Some(vec![
                Dep {
                    head: TokenID::Single(2),
                    rel: "nsubj".to_string()
                },
                Dep {
                    head: TokenID::Single(4),
                    rel: "nsubj".to_string()
                }
            ]),
            misc: None
        }
    )
}
