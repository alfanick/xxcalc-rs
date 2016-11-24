#![feature(test)]
extern crate test;

pub mod polynomial;
#[macro_use]
pub mod tokenizer;
pub mod parser;
pub mod evaluator;
pub mod calculator;
pub mod polynomial_calculator;
pub mod linear_solver;

#[derive(Debug, PartialEq)]
pub enum ParsingError {
  UnknownOperator(char, usize),
  UnknownToken(usize),
  MissingBracket(usize),
  EmptyExpression
}

#[derive(Debug, PartialEq)]
pub enum EvaluationError {
  UnknownSymbol(String, usize),
  ArgumentMissing(String, usize, usize),
  MultipleExpressions,
  ConflictingName(String),
  PolynomialError(polynomial::PolynomialError),
  SolvingError(linear_solver::SolvingError),
  NonConstantExponent,
  NonNaturalExponent
}

pub trait StringProcessor {
  fn process(self: &mut Self, line: &str) -> &Tokens;
}

pub trait TokensProcessor {
  fn process(&mut self, tokens: &Tokens) -> Result<&Tokens, ParsingError>;
}

pub trait TokensReducer {
  fn process(&self, tokens: &Tokens) -> Result<polynomial::Polynomial, EvaluationError>;
}

use std::ops::Index;
use std::collections::BTreeMap;

pub struct Tokens {
  pub tokens: TokenList,
  pub identifiers: Identifiers,
  lookup: BTreeMap<String, usize>
}

pub type TokenList = Vec<(usize, Token)>;
pub type Identifiers = Vec<String>;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
  BracketOpening,
  BracketClosing,
  Separator,
  Number(f64),
  Operator(char),
  Identifier(usize),
  Skip,
  Unknown
}

impl Index<usize> for Tokens {
  type Output = (usize, Token);

  fn index(&self, idx: usize) -> &(usize, Token) {
    &self.tokens[idx]
  }
}

impl Tokens {
  pub fn new(i_cap: Option<usize>) -> Tokens {
    Tokens {
      tokens: TokenList::with_capacity(10),
      identifiers: Identifiers::with_capacity(i_cap.unwrap_or(0)),
      lookup: BTreeMap::new()
    }
  }

  #[inline(always)]
  pub fn clear(&mut self) {
    self.tokens.clear()
  }

  #[inline(always)]
  pub fn push(&mut self, position: usize, token: Token) {
    self.tokens.push((position, token))
  }

  #[inline]
  pub fn push_identifier(&mut self, position: usize, value: &String) {
    let idx = if let Some(&id) = self.lookup.get(value) {
      id
    } else {
      if let Some(&id) = self.lookup.get(&value.to_lowercase()) {
        let _ = self.lookup.insert(value.clone(), id);
        id
      } else {
        let _ = self.lookup.insert(value.to_lowercase(), self.identifiers.len());
        self.identifiers.push(value.clone());
        self.identifiers.len() - 1
      }
    };
    self.push(position, Token::Identifier(idx));
  }
}

