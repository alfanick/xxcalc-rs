//! `Tokenizer` is a `StringProcessor`, it takes string expression
//! and converts it into Tokens for further processing.

use super::*;

/// `Tokenizer` performs the very first step of parsing mathematical
/// expression into `Tokens`. These tokens can be then processed by
/// `TokensProcessor`.
///
/// `Tokenizer` is a state machine, which can be reused multiple
/// times. Internally it stores a buffer of Tokens, which can
/// be reused multiple times without requesting new memory from
/// the operating system. If Tokenizer lives long enough this
/// behaviour can greatly reduce time wasted on mallocs.
///
/// # Examples
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::{StringProcessor, Token};
/// let mut tokenizer = Tokenizer::default();
///
/// {
///   let tokens = tokenizer.process("2.0+2");
///   assert_eq!(tokens[0], (0, Token::Number(2.0)));
///   assert_eq!(tokens[1], (3, Token::Operator('+')));
///   assert_eq!(tokens[2], (4, Token::Number(2.0)));
/// }
///
/// {
///   let tokens = tokenizer.process("x+log10(100)+x");
///   assert_eq!(tokens[0], (0, Token::Identifier(0)));
///   assert_eq!(tokens.identifiers[0], "x");
///   assert_eq!(tokens[1], (1, Token::Operator('+')));
///   assert_eq!(tokens[2], (2, Token::Identifier(1)));
///   assert_eq!(tokens.identifiers[1], "log10");
///   assert_eq!(tokens[3], (7, Token::BracketOpening));
///   assert_eq!(tokens[4], (8, Token::Number(100.0)));
///   assert_eq!(tokens[5], (11, Token::BracketClosing));
///   assert_eq!(tokens[6], (12, Token::Operator('+')));
///   assert_eq!(tokens[7], (13, Token::Identifier(0)));
/// }
/// ```
pub struct Tokenizer {
  /// Tokens storage (its capacity is stored between runs)
  tokens: Tokens,

  /// Start position of value
  value_position: usize,
  /// String representation of current value
  value: String,

  /// Current state of tokenizer
  state: State,
  /// Previous state of tokenizer
  previous_state: State,

}

/// Creates a new default Tokenizer.
///
/// Such tokenizer is optimized (but not limited) for
/// values up to 10 characters and up to 10 tokens.
/// However these are default space capacities and they
/// can extend dynamically.
impl Default for Tokenizer {
  #[inline]
  fn default() -> Tokenizer {
    Tokenizer {
      tokens: Tokens::new(Some(10)),
      value_position: 0,
      value: String::with_capacity(10),
      state: State::Front,
      previous_state: State::General
    }
  }
}

/// This is a main processing unit in the tokenizer.
/// It takes a string expression and creates a list of
/// tokens representing this string using a state machine.
///
/// This tokenizer supports floating point numbers in traditional
/// and scientific notation (as well as shorthand point notation),
/// text identifiers and operators such as `+`, `-`, `*`, `/`, `^`
/// and `=`. Parentheses `()` and comma `,` are supported too.
/// Whitespaces are always skipped, not recognized characters
/// are wrapped into Unknown token.
///
/// Signed numbers are detected when they cannot be mistaken
/// for operators `+` or `-`. Implicit multiplication before an
/// identifier or a parantheses is replaced with explicit multiplication
/// with `*` operator.
///
/// # Extending
///
/// New features can be add to tokenizer by either embedding this
/// tokenizer into new one and replacing Unknown tokens with some
/// other tokens or by implementing a `TokensProcessor` which takes
/// output of this tokenizer and replaces Unknown tokens or some
/// combination of tokens with other ones.
///
/// # State machine
///
/// Complete, hand-designed state machine used by this `StringProcessor`
/// can be seen in the image below:
///
/// ![Tokenizer State Machine](http://public.amadeusz.me/documents/tokenizer.svg)
impl StringProcessor for Tokenizer {
  fn process(&mut self, line: &str) -> &Tokens {
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
               self.state == State::General ||
               self.state == State::Operator => {
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
          token = Token::Unknown(character);
          self.state = State::General;
        }
      }

      self.push_number_or_identifier(Some(position));

      if token != Token::Skip {
        self.tokens.push(position, token);
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
          self.tokens.push(self.value_position,
                                Token::Number(self.value.parse().unwrap()));
          self.value.clear();
        } else
        if self.previous_state == State::Identifier {
          self.tokens.push_identifier(self.value_position, &self.value);
          self.value.clear();
        }
      }
    } else
    if self.state == State::Number ||
       self.state == State::NumberExponent {
      self.tokens.push(self.value_position,
                            Token::Number(self.value.parse().unwrap()));
    } else
    if self.state == State::Identifier {
      self.tokens.push_identifier(self.value_position, &self.value);
    }
  }

  #[inline(always)]
  fn implicit_multiplication(&mut self, position: usize, character: char) {
    if (character == '(' || character.is_alphabetic()) &&
       (self.previous_state == State::NumberSign ||
        self.previous_state == State::NumberExponent ||
        (self.previous_state == State::Number && character != 'e')) {

      self.tokens.push(self.value_position,
                         if self.previous_state == State::NumberSign {
                           Token::Number(if self.value.starts_with('-') {-1.0} else {1.0})
                         } else {
                           Token::Number(self.value.parse().unwrap())
                         });

      self.value.clear();
      self.tokens.push(self.value_position, Token::Operator('*'));
      self.value_position = position;
      self.previous_state = State::General;
    }
  }
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

macro_rules! tokenize {
  ($x:expr) => (Tokenizer::default().process($x).to_owned())
}

macro_rules! tokenize_ref {
  ($x:expr) => (Tokenizer::default().process($x))
}

#[cfg(test)]
mod tests {
  use Token;
  use StringProcessor;
  use tokenizer::*;

  #[test]
  fn test_brackets() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("(").tokens.first(), Some(&(0, Token::BracketOpening)));
    assert_eq!(tokenizer.process(")").tokens.first(), Some(&(0, Token::BracketClosing)));
  }

  #[test]
  fn test_operators() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("2+2").tokens.iter().skip(1).next(), Some(&(1, Token::Operator('+'))));
    assert_eq!(tokenizer.process("2-2").tokens.iter().skip(1).next(), Some(&(1, Token::Operator('-'))));
    assert_eq!(tokenizer.process("*").tokens.first(), Some(&(0, Token::Operator('*'))));
    assert_eq!(tokenizer.process("/").tokens.first(), Some(&(0, Token::Operator('/'))));
    assert_eq!(tokenizer.process("=").tokens.first(), Some(&(0, Token::Operator('='))));
    assert_eq!(tokenizer.process("^").tokens.first(), Some(&(0, Token::Operator('^'))));
  }

  #[test]
  fn test_identifiers() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("x").identifiers[0], "x");
    assert_eq!(tokenizer.process("x123x").identifiers[1], "x123x");
    assert_eq!(tokenizer.process("_foo_bar").identifiers[2], "_foo_bar");
    assert_eq!(tokenizer.process("_foo_123").identifiers[3], "_foo_123");
    assert_eq!(tokenizer.process("x").tokens[0], (0, Token::Identifier(0)));
    assert_eq!(tokenizer.process("_FOO_123").tokens[0], (0, Token::Identifier(3)));
  }

  #[test]
  fn test_numbers() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("1").tokens.first(), Some(&(0, Token::Number(1.0))));
    assert_eq!(tokenizer.process("1.23").tokens.first(), Some(&(0, Token::Number(1.23))));
    assert_eq!(tokenizer.process(".23").tokens.first(), Some(&(0, Token::Number(0.23))));
  }

  #[test]
  fn test_numbers_scientific() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("1e23").tokens.first(), Some(&(0, Token::Number(1.0e23))));
    assert_eq!(tokenizer.process("1e-23").tokens.first(), Some(&(0, Token::Number(1.0e-23))));
    assert_eq!(tokenizer.process("1.01e+23").tokens.first(), Some(&(0, Token::Number(1.01e23))));
  }

  #[test]
  fn test_expressions() {
    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2+2");
    assert_eq!(t.tokens[0], ((0, Token::Number(2.0))));
    assert_eq!(t.tokens[1], ((1, Token::Operator('+'))));
    assert_eq!(t.tokens[2], ((2, Token::Number(2.0))));

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2+x");
    assert_eq!(t.tokens[0], ((0, Token::Number(2.0))));
    assert_eq!(t.tokens[1], ((1, Token::Operator('+'))));
    assert_eq!(t.tokens[2], ((2, Token::Identifier(0))));
    assert_eq!(t.identifiers[0], "x".to_string());

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("x=2");
    assert_eq!(t.identifiers[0], "x".to_string());
    assert_eq!(t.tokens[0], ((0, Token::Identifier(0))));
    assert_eq!(t.tokens[1], ((1, Token::Operator('='))));
    assert_eq!(t.tokens[2], ((2, Token::Number(2.0))));
  }

  #[test]
  fn test_numbers_signed() {
    let mut tokenizer = Tokenizer::default();
    assert_eq!(tokenizer.process("-2").tokens.first(), Some(&(0, Token::Number(-2.0))));
    assert_eq!(tokenizer.process(" -2").tokens.first(), Some(&(0, Token::Number(-2.0))));
    assert_eq!(tokenizer.process("+2").tokens.first(), Some(&(0, Token::Number(2.0))));

    assert_eq!(tokenizer.process("(-2)").tokens.iter().skip(1).next(), Some(&(1, Token::Number(-2.0))));
    assert_eq!(tokenizer.process("( -2)").tokens.iter().skip(1).next(), Some(&(1, Token::Number(-2.0))));
    assert_eq!(tokenizer.process("(+2)").tokens.iter().skip(1).next(), Some(&(1, Token::Number(2.0))));

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2-+2");
    assert_eq!(t.tokens[0], ((0, Token::Number(2.0))));
    assert_eq!(t.tokens[1], ((1, Token::Operator('-'))));
    assert_eq!(t.tokens[2], ((2, Token::Number(2.0))));

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2--2");
    assert_eq!(t.tokens[0], ((0, Token::Number(2.0))));
    assert_eq!(t.tokens[1], ((1, Token::Operator('-'))));
    assert_eq!(t.tokens[2], ((2, Token::Number(-2.0))));
  }

  #[test]
  fn test_implicit_multiplication() {
    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("2--x");
    assert_eq!(t.tokens[0], ((0, Token::Number(2.0))));
    assert_eq!(t.tokens[1], ((1, Token::Operator('-'))));
    assert_eq!(t.tokens[2], ((2, Token::Number(-1.0))));
    assert_eq!(t.tokens[3], ((2, Token::Operator('*'))));
    assert_eq!(t.tokens[4], ((3, Token::Identifier(0))));
    assert_eq!(t.identifiers[0], "x".to_string());

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("-2x");
    assert_eq!(t.tokens[0], ((0, Token::Number(-2.0))));
    assert_eq!(t.tokens[1], ((0, Token::Operator('*'))));
    assert_eq!(t.tokens[2], ((2, Token::Identifier(0))));
    assert_eq!(t.identifiers[0], "x".to_string());

    let mut tokenizer = Tokenizer::default();
    let t = tokenizer.process("-2(4)");
    assert_eq!(t.tokens[0], ((0, Token::Number(-2.0))));
    assert_eq!(t.tokens[1], ((0, Token::Operator('*'))));
    assert_eq!(t.tokens[2], ((2, Token::BracketOpening)));
    assert_eq!(t.tokens[3], ((3, Token::Number(4.0))));
    assert_eq!(t.tokens[4], ((4, Token::BracketClosing)));

  }
}
