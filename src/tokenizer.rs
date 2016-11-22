pub type TokenList = Vec<(usize, Token)>;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
  BracketOpening,
  BracketClosing,
  Separator,
  Number(f64),
  Operator(char),
  Identifier(String),
  Skip,
  Unknown
}

pub struct Tokenizer {
  tokens: TokenList,

  value_position: usize,
  value: String,

  state: State,
  previous_state: State
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
      tokens: TokenList::with_capacity(10),
      value_position: 0,
      value: String::with_capacity(10),
      state: State::Front,
      previous_state: State::General
    }
  }
}

pub trait StringProcessor {
  fn process(self: &mut Self, line: &str) -> &TokenList;
}

impl StringProcessor for Tokenizer {
  fn process(&mut self, line: &str) -> &TokenList {
    self.tokens.clear();
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
        '-' | '+' if self.state == State::NumberExponent => {
          self.value.push(character);
          self.state = State::NumberExponent;
        },
        '-' | '+' if self.state == State::Front ||
                     self.state == State::Operator => {
          self.value.push(character);
          self.state = State::NumberSign;
        },
        '+' | '-' | '/' | '*' | '^' | '=' => {
          token = Token::Operator(character);
          self.state = State::Operator;
        },
        '_' if self.state == State::Front ||
               self.state == State::General ||
               self.state == State::Identifier => {
          self.value.push(character);
          self.state = State::Identifier;
        },
        'e' if self.state == State::Number => {
          self.value.push(character);
          self.state = State::NumberExponent;
        },
        '.' if self.state == State::Number ||
               self.state == State::General ||
               self.state == State::Front => {
          self.value.push(character);
          self.state = State::Number;
        },
        _ if character.is_numeric() => {
          self.value.push(character);
          if self.state == State::Front ||
             self.state == State::General ||
             self.state == State::Operator ||
             self.state == State::NumberSign {
            self.state = State::Number;
          }
        },
        _ if character.is_alphabetic() => {
          self.value.push(character);
          self.state = State::Identifier;
        },
        _ => {
          token = Token::Unknown;
          self.state = State::General;
        }
      }

      self.push_number_or_identifier(Some(position));

      if token != Token::Skip {
        self.tokens.push((position, token));
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
      if self.state == State::Front || self.state == State::General || self.state == State::Operator {
        if self.previous_state == State::Number ||
           self.previous_state == State::NumberExponent {
          self.tokens.push((self.value_position,
                                 Token::Number(self.value.parse().unwrap())));
          self.value.clear();
        } else
        if self.previous_state == State::Identifier {
          self.tokens.push((self.value_position,
                                 Token::Identifier(self.value.to_lowercase())));
          self.value.clear();
        }
      }
    } else {
      if self.state == State::Number ||
         self.state == State::NumberExponent {
        self.tokens.push((self.value_position,
                               Token::Number(self.value.parse().unwrap())));
      } else
      if self.state == State::Identifier {
        self.tokens.push((self.value_position,
                               Token::Identifier(self.value.to_lowercase())));
      }
    }
  }

  #[inline(always)]
  fn implicit_multiplication(&mut self, position: usize, character: char) {
    if character == '(' || character.is_alphabetic() {
      if self.previous_state == State::NumberSign ||
         self.previous_state == State::NumberExponent ||
         (self.previous_state == State::Number && character != 'e') {

        self.tokens.push((self.value_position,
                               if self.previous_state == State::NumberSign {
                                 Token::Number(if self.value.starts_with('-') {-1.0} else {1.0})
                               } else {
                                 Token::Number(self.value.parse().unwrap())
                               }));

        self.value.clear();
        self.tokens.push((self.value_position, Token::Operator('*')));
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
    assert_eq!(tokenize!("(").first(), Some(&(0, Token::BracketOpening)));
    assert_eq!(tokenize!(")").first(), Some(&(0, Token::BracketClosing)));
  }

  #[test]
  fn test_operators() {
    assert_eq!(tokenize!("2+2").iter().skip(1).next(), Some(&(1, Token::Operator('+'))));
    assert_eq!(tokenize!("2-2").iter().skip(1).next(), Some(&(1, Token::Operator('-'))));
    assert_eq!(tokenize!("*").first(), Some(&(0, Token::Operator('*'))));
    assert_eq!(tokenize!("/").first(), Some(&(0, Token::Operator('/'))));
    assert_eq!(tokenize!("=").first(), Some(&(0, Token::Operator('='))));
    assert_eq!(tokenize!("^").first(), Some(&(0, Token::Operator('^'))));
  }

  #[test]
  fn test_identifiers() {
    assert_eq!(tokenize!("x").first(), Some(&(0, Token::Identifier("x".to_string()))));
    assert_eq!(tokenize!("x123x").first(), Some(&(0, Token::Identifier("x123x".to_string()))));
    assert_eq!(tokenize!("_foo_bar").first(), Some(&(0, Token::Identifier("_foo_bar".to_string()))));
    assert_eq!(tokenize!("_foo_123").first(), Some(&(0, Token::Identifier("_foo_123".to_string()))));
  }

  #[test]
  fn test_numbers() {
    assert_eq!(tokenize!("1").first(), Some(&(0, Token::Number(1.0))));
    assert_eq!(tokenize!("1.23").first(), Some(&(0, Token::Number(1.23))));
    assert_eq!(tokenize!(".23").first(), Some(&(0, Token::Number(0.23))));
  }

  #[test]
  fn test_numbers_scientific() {
    assert_eq!(tokenize!("1e23").first(), Some(&(0, Token::Number(1.0e23))));
    assert_eq!(tokenize!("1e-23").first(), Some(&(0, Token::Number(1.0e-23))));
    assert_eq!(tokenize!("1.01e+23").first(), Some(&(0, Token::Number(1.01e23))));
  }

  #[test]
  fn test_expressions() {
    let mut t = tokenize!("2+2");
    assert_eq!(t.remove(0), ((0, Token::Number(2.0))));
    assert_eq!(t.remove(0), ((1, Token::Operator('+'))));
    assert_eq!(t.remove(0), ((2, Token::Number(2.0))));

    let mut t = tokenize!("2+x");
    assert_eq!(t.remove(0), ((0, Token::Number(2.0))));
    assert_eq!(t.remove(0), ((1, Token::Operator('+'))));
    assert_eq!(t.remove(0), ((2, Token::Identifier("x".to_string()))));

    let mut t = tokenize!("x=2");
    assert_eq!(t.remove(0), ((0, Token::Identifier("x".to_string()))));
    assert_eq!(t.remove(0), ((1, Token::Operator('='))));
    assert_eq!(t.remove(0), ((2, Token::Number(2.0))));
  }

  #[test]
  fn test_numbers_signed() {
    assert_eq!(tokenize!("-2").first(), Some(&(0, Token::Number(-2.0))));
    assert_eq!(tokenize!(" -2").first(), Some(&(0, Token::Number(-2.0))));
    assert_eq!(tokenize!("+2").first(), Some(&(0, Token::Number(2.0))));

    assert_eq!(tokenize!("(-2)").iter().skip(1).next(), Some(&(1, Token::Number(-2.0))));
    assert_eq!(tokenize!("( -2)").iter().skip(1).next(), Some(&(1, Token::Number(-2.0))));
    assert_eq!(tokenize!("(+2)").iter().skip(1).next(), Some(&(1, Token::Number(2.0))));

    let mut t = tokenize!("2-+2");
    assert_eq!(t.remove(0), ((0, Token::Number(2.0))));
    assert_eq!(t.remove(0), ((1, Token::Operator('-'))));
    assert_eq!(t.remove(0), ((2, Token::Number(2.0))));

    let mut t = tokenize!("2--2");
    assert_eq!(t.remove(0), ((0, Token::Number(2.0))));
    assert_eq!(t.remove(0), ((1, Token::Operator('-'))));
    assert_eq!(t.remove(0), ((2, Token::Number(-2.0))));
  }

  #[test]
  fn test_implicit_multiplication() {
    let mut t = tokenize!("2--x");
    assert_eq!(t.remove(0), ((0, Token::Number(2.0))));
    assert_eq!(t.remove(0), ((1, Token::Operator('-'))));
    assert_eq!(t.remove(0), ((2, Token::Number(-1.0))));
    assert_eq!(t.remove(0), ((2, Token::Operator('*'))));
    assert_eq!(t.remove(0), ((3, Token::Identifier("x".to_string()))));

    let mut t = tokenize!("-2x");
    assert_eq!(t.remove(0), ((0, Token::Number(-2.0))));
    assert_eq!(t.remove(0), ((0, Token::Operator('*'))));
    assert_eq!(t.remove(0), ((2, Token::Identifier("x".to_string()))));

    let mut t = tokenize!("-2(4)");
    assert_eq!(t.remove(0), ((0, Token::Number(-2.0))));
    assert_eq!(t.remove(0), ((0, Token::Operator('*'))));
    assert_eq!(t.remove(0), ((2, Token::BracketOpening)));
    assert_eq!(t.remove(0), ((3, Token::Number(4.0))));
    assert_eq!(t.remove(0), ((4, Token::BracketClosing)));

  }
}
