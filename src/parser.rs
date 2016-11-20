use tokenizer::TokenList;
use std::collections::BTreeMap;

enum OperatorAssociativity {
  Left,
  Right
}

struct Operator(i64, OperatorAssociativity);

pub struct Parser {
  operators: BTreeMap<char, Operator>;
}

impl Parser {

}