pub struct Tokens(pub TokenList, pub Identifiers);

pub type TokenList = Vec<(usize, Token)>;
pub type Identifiers = Vec<String>;

use std::collections::BTreeMap;

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

pub struct Tokenizer {
  tokens: Tokens,

  value_position: usize,
  value: String,

  state: State,
  previous_state: State,

  lookup: BTreeMap<String, usize>
}

#[derive(PartialEq, Copy, Clone, Debug)]
enum State {
  Front,
  General,
  Identifier,
  NumberSign,
  Number,
  NumberExponent,
  Operator
}

impl Default for Tokenizer {
  #[inline]
  fn default() -> Tokenizer {
    Tokenizer {
      tokens: Tokens(TokenList::with_capacity(10), Identifiers::with_capacity(10)),
      value_position: 0,
      value: String::with_capacity(10),
      state: State::Front,
      previous_state: State::General,
      lookup: BTreeMap::new()
    }
  }
}

pub trait StringProcessor {
  fn process(self: &mut Self, line: &str) -> &Tokens;
}

impl StringProcessor for Tokenizer {
  fn process(&mut self, line: &str) -> &Tokens {
    // println!("cap: {}", self.tokens.capacity());
    self.tokens.0.clear();
    self.value_position = 0;
    self.value.clear();
    self.state = State::Front;
    self.previous_state = State::General;

    for (position, character) in line.chars().enumerate() {
      if character.is_whitespace() {
        continue;
      }

      let mut token = Token::Skip;
      self.previous_state = self.state;

      self.implicit_multiplication(position, character);

      match character {
        _ if character.is_numeric() => {
          self.value.push(character);
          if self.state == State::Front ||
             self.state == State::General ||
             self.state == State::Operator ||
             self.state == State::NumberSign {
            self.state = State::Number;
          }
        },
        '-' | '+' if self.state == State::Front ||
                     self.state == State::Operator => {
          self.value.push(character);
          self.state = State::NumberSign;
        },
        '-' | '+' if self.state == State::NumberExponent => {
          self.value.push(character);
          self.state = State::NumberExponent;
        },
        '+' | '-' | '/' | '*' | '^' | '=' => {
          token = Token::Operator(character);
          self.state = State::Operator;
        },
        'e' if self.state == State::Number => {
          self.value.push(character);
          self.state = State::NumberExponent;
        },
        _ if character.is_alphabetic() => {
          self.value.push(character);
          self.state = State::Identifier;
        },
        '_' if self.state == State::Identifier ||
               self.state == State::Front ||
               self.state == State::General => {
          self.value.push(character);
          self.state = State::Identifier;
        },
        '.' if self.state == State::Number ||
               self.state == State::Front ||
               self.state == State::General => {
          self.value.push(character);
          self.state = State::Number;
        },
        '(' => {
          token = Token::BracketOpening;
          self.state = State::Front;
        },
        ')' => {
          token = Token::BracketClosing;
          self.state = State::General;
        },
        ',' => {
          token = Token::Separator;
          self.state = State::Front;
        },
        _ => {
          token = Token::Unknown;
          self.state = State::General;
        }
      }

      self.push_number_or_identifier(Some(position));

      if token != Token::Skip {
        self.tokens.0.push((position, token));
        self.value_position = position + 1;
      }
    }

    self.push_number_or_identifier(None);

    &self.tokens
  }
}

impl Tokenizer {
  #[inline(always)]
  fn push_number_or_identifier(&mut self, position: Option<usize>) {
    if position.is_some() {
      if self.state == State::Operator ||
         self.state == State::Front ||
         self.state == State::General {
        if self.previous_state == State::Number ||
           self.previous_state == State::NumberExponent {
          self.tokens.0.push((self.value_position,
                              Token::Number(self.value.parse().unwrap())));
          self.value.clear();
        } else
        if self.previous_state == State::Identifier {
          let idx = if let Some(&id) = self.lookup.get(&self.value) {
            id
          } else {
            if let Some(&id) = self.lookup.get(&self.value.to_lowercase()) {
              let _ = self.lookup.insert(self.value.clone(), id);
              id
            } else {
              let _ = self.lookup.insert(self.value.to_lowercase(), self.tokens.1.len());
              self.tokens.1.push(self.value.clone());
              self.tokens.1.len() - 1
            }
          };
          self.tokens.0.push((self.value_position, Token::Identifier(idx)));
          self.value.clear();
        }
      }
    } else {
      if self.state == State::Number ||
         self.state == State::NumberExponent {
        self.tokens.0.push((self.value_position,
                            Token::Number(self.value.parse().unwrap())));
      } else
      if self.state == State::Identifier {
        let idx = if let Some(&id) = self.lookup.get(&self.value) {
          id
        } else {
          if let Some(&id) = self.lookup.get(&self.value.to_lowercase()) {
            let _ = self.lookup.insert(self.value.clone(), id);
            id
          } else {
            let _ = self.lookup.insert(self.value.to_lowercase(), self.tokens.1.len());
            self.tokens.1.push(self.value.clone());
            self.tokens.1.len() - 1
          }
        };
        self.tokens.0.push((self.value_position, Token::Identifier(idx)));
      }
    }
  }

  #[inline(always)]
  fn implicit_multiplication(&mut self, position: usize, character: char) {
    if character == '(' || character.is_alphabetic() {
      if self.previous_state == State::NumberSign ||
         self.previous_state == State::NumberExponent ||
         (self.previous_state == State::Number && character != 'e') {

        self.tokens.0.push((self.value_position,
                               if self.previous_state == State::NumberSign {
                                 Token::Number(if self.value.starts_with('-') {-1.0} else {1.0})
                               } else {
                                 Token::Number(self.value.parse().unwrap())
                               }));

        self.value.clear();
        self.tokens.0.push((self.value_position, Token::Operator('*')));
        self.value_position = position;
        self.previous_state = State::General;
      }
    }
  }
}

macro_rules! tokenize {
  ($x:expr) => (Tokenizer::default().process($x).to_owned())
}

macro_rules! tokenize_ref {
  ($x:expr) => (Tokenizer::default().process($x))
}

#[cfg(test)]
mod tests {
  use tokenizer::*;

  #[test]
  fn test_brackets() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("(").0.first(), Some(&(0, Token::BracketOpening)));
    assert_eq!(tokenizer.process(")").0.first(), Some(&(0, Token::BracketClosing)));
  }

  #[test]
  fn test_operators() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("2+2").0.iter().skip(1).next(), Some(&(1, Token::Operator('+'))));
    assert_eq!(tokenizer.process("2-2").0.iter().skip(1).next(), Some(&(1, Token::Operator('-'))));
    assert_eq!(tokenizer.process("*").0.first(), Some(&(0, Token::Operator('*'))));
    assert_eq!(tokenizer.process("/").0.first(), Some(&(0, Token::Operator('/'))));
    assert_eq!(tokenizer.process("=").0.first(), Some(&(0, Token::Operator('='))));
    assert_eq!(tokenizer.process("^").0.first(), Some(&(0, Token::Operator('^'))));
  }

  #[test]
  fn test_identifiers() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("x").1[0], "x");
    assert_eq!(tokenizer.process("x123x").1[1], "x123x");
    assert_eq!(tokenizer.process("_foo_bar").1[2], "_foo_bar");
    assert_eq!(tokenizer.process("_foo_123").1[3], "_foo_123");
    assert_eq!(tokenizer.process("x").0[0], (0, Token::Identifier(0)));
    assert_eq!(tokenizer.process("_FOO_123").0[0], (0, Token::Identifier(3)));
  }

  #[test]
  fn test_numbers() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("1").0.first(), Some(&(0, Token::Number(1.0))));
    assert_eq!(tokenizer.process("1.23").0.first(), Some(&(0, Token::Number(1.23))));
    assert_eq!(tokenizer.process(".23").0.first(), Some(&(0, Token::Number(0.23))));
  }

  #[test]
  fn test_numbers_scientific() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("1e23").0.first(), Some(&(0, Token::Number(1.0e23))));
    assert_eq!(tokenizer.process("1e-23").0.first(), Some(&(0, Token::Number(1.0e-23))));
    assert_eq!(tokenizer.process("1.01e+23").0.first(), Some(&(0, Token::Number(1.01e23))));
  }

  #[test]
  fn test_expressions() {
    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2+2");
    assert_eq!(t.0[0], ((0, Token::Number(2.0))));
    assert_eq!(t.0[1], ((1, Token::Operator('+'))));
    assert_eq!(t.0[2], ((2, Token::Number(2.0))));

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2+x");
    assert_eq!(t.0[0], ((0, Token::Number(2.0))));
    assert_eq!(t.0[1], ((1, Token::Operator('+'))));
    assert_eq!(t.0[2], ((2, Token::Identifier(0))));
    assert_eq!(t.1[0], "x".to_string());

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("x=2");
    assert_eq!(t.1[0], "x".to_string());
    assert_eq!(t.0[0], ((0, Token::Identifier(0))));
    assert_eq!(t.0[1], ((1, Token::Operator('='))));
    assert_eq!(t.0[2], ((2, Token::Number(2.0))));
  }

  #[test]
  fn test_numbers_signed() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("-2").0.first(), Some(&(0, Token::Number(-2.0))));
    assert_eq!(tokenizer.process(" -2").0.first(), Some(&(0, Token::Number(-2.0))));
    assert_eq!(tokenizer.process("+2").0.first(), Some(&(0, Token::Number(2.0))));

    assert_eq!(tokenizer.process("(-2)").0.iter().skip(1).next(), Some(&(1, Token::Number(-2.0))));
    assert_eq!(tokenizer.process("( -2)").0.iter().skip(1).next(), Some(&(1, Token::Number(-2.0))));
    assert_eq!(tokenizer.process("(+2)").0.iter().skip(1).next(), Some(&(1, Token::Number(2.0))));

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2-+2");
    assert_eq!(t.0[0], ((0, Token::Number(2.0))));
    assert_eq!(t.0[1], ((1, Token::Operator('-'))));
    assert_eq!(t.0[2], ((2, Token::Number(2.0))));

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2--2");
    assert_eq!(t.0[0], ((0, Token::Number(2.0))));
    assert_eq!(t.0[1], ((1, Token::Operator('-'))));
    assert_eq!(t.0[2], ((2, Token::Number(-2.0))));
  }

  #[test]
  fn test_implicit_multiplication() {
    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2--x");
    assert_eq!(t.0[0], ((0, Token::Number(2.0))));
    assert_eq!(t.0[1], ((1, Token::Operator('-'))));
    assert_eq!(t.0[2], ((2, Token::Number(-1.0))));
    assert_eq!(t.0[3], ((2, Token::Operator('*'))));
    assert_eq!(t.0[4], ((3, Token::Identifier(0))));
    assert_eq!(t.1[0], "x".to_string());

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("-2x");
    assert_eq!(t.0[0], ((0, Token::Number(-2.0))));
    assert_eq!(t.0[1], ((0, Token::Operator('*'))));
    assert_eq!(t.0[2], ((2, Token::Identifier(0))));
    assert_eq!(t.1[0], "x".to_string());

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("-2(4)");
    assert_eq!(t.0[0], ((0, Token::Number(-2.0))));
    assert_eq!(t.0[1], ((0, Token::Operator('*'))));
    assert_eq!(t.0[2], ((2, Token::BracketOpening)));
    assert_eq!(t.0[3], ((3, Token::Number(4.0))));
    assert_eq!(t.0[4], ((4, Token::BracketClosing)));

  }
}

#[cfg(test)]
pub mod benchmarks {
  use super::*;
  use test::Bencher;

  pub fn add_sub_gen(n: usize) -> String {
    (0..n).map(|x| format!("{}-{}+", x, x).to_string()).fold(String::new(), |a, x| a+&x)+"0"
  }

  #[bench]
  #[ignore]
  fn bench_tokenizer(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      (0..10).fold(0, |a, x| a + x + tokenizer.process(add_sub_r).0.len())
    });
  }

  #[bench]
  #[ignore]
  fn bench_tokenizer_without_arena(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);

    b.iter(|| {
      (0..10).fold(0, |a, x| {
        let mut tokenizer = Tokenizer::default();
        a + x + tokenizer.process(add_sub_r).0.len()
      })
    });
  }

  #[bench]
  fn bench_tokenizer_numbers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      tokenizer.process("3.1415926535897932").0.len()
    });
  }

  #[bench]
  fn bench_tokenizer_short_numbers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      tokenizer.process("2").0.len()
    });
  }

  #[bench]
  fn bench_tokenizer_identifiers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      tokenizer.process("_lorem_ipsum_dolor").0.len()
    });
  }

  #[bench]
  fn bench_tokenizer_short_identifiers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      tokenizer.process("x").0.len()
    });
  }

  #[bench]
  fn bench_tokenizer_brackets(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      tokenizer.process("(").0.len()
    });
  }

  #[bench]
  fn bench_tokenizer_operators(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.iter(|| {
      tokenizer.process("+").0.len()
    });
  }
}
