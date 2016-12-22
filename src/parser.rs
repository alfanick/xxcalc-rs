//! `Parser` is a `TokensProcessor`, it takes `Tokens` in a classical
//! infix form and transforms them into Reverse Polish Notation
//! form for further evaluation.

use super::*;
use std::collections::BTreeMap;

/// Defines operator associativity.
///
/// If two operators have the same precedence (priority), the order
/// of their evaluation is defined by their associativity.
/// A left-associative operator evaluates a left hand side before evaluating
/// the right hand side. A right-associative operator evaluates a RHS before
/// evaluating LHS.
#[derive(PartialEq, Debug)]
pub enum OperatorAssociativity {
  /// Left associativity - `a O b O c` is evaluated as `(a O b) O c`
  Left,
  /// Right associativity - `a O b O c` is evaluated as `a O (b O c)`
  Right
}

/// Stores operator precedence and its associativity.
///
/// Both features are essential when parsing mathematical expressions.
/// An operator precedence defines its priority, operators with larger
/// precedence are evaluated before operators with smaller precedence.
/// An associativity resolves conflicts when two operators are of the
/// same precedence - a left-associative operator evaluates LHS before
/// RHS, while a right-associative operator evalutes RHS before LHS.
///
/// Knowledge of these features is required to properly convert infix
/// form into RPN.
#[derive(PartialEq, Debug)]
pub struct Operator(i64, OperatorAssociativity);

impl Operator {
  /// Creates a new operator with given precedence and associativity.
  pub fn new(p: i64, a: OperatorAssociativity) -> Operator {
    Operator(p, a)
  }
}

/// `Parser` takes `Tokens` in infix form and transforms them into
/// Reverse Polish Notation. After such transformation tokens
/// can be processed by `TokensReducer`.
///
/// Parser stores registered operators (with their precedence and
/// associativity) between multiple executions. Furthermore an
/// output buffer of `Tokens` is kept internally, so it can be reused
/// without allocating new memory from the operating system. If
/// Parser lives long enough this behaviour can greatly reduce
/// time wasted on mallocs.
///
/// # Examples
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
/// # use xxcalc::{Token, StringProcessor, TokensProcessor};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
///
/// parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
///
/// let tokenized = tokenizer.process("2+2");
/// let parsed = parser.process(tokenized).unwrap();
///
/// assert_eq!(parsed.tokens, [(0, Token::Number(2.0)),
///                            (2, Token::Number(2.0)),
///                            (1, Token::Operator('+'))]);
/// ```
///
/// # Extending
///
/// One could embed the parser inside another `TokensProcessor` and initialize
/// it there with some default operators.
pub struct Parser {
  operators: BTreeMap<char, Operator>,
  output: Tokens
}

/// Creates a new default Parser.
///
/// Such parser is not ready to parse complex infix notation
/// by default. No operators are registered by default, one
/// must define operators with their precedence and associativity
/// to be able of parsing complex mathematical expressions.
impl Default for Parser {
  fn default() -> Parser {
    Parser::new()
  }
}

/// This is a main processing unit in the parser. It takes
/// a tokens in infix form and converts them to RPN using
/// Dijsktra's shunting-yard algorithm.
///
/// Before processing expressions more complex than trivial
/// identifiers or numbers, operators must be registered.
///
/// This parser supports two argument operators and multiple
/// argument functions. Function arguments must be declared
/// between opening and closing bracket tokens, with their
/// arguments separated using separator token.
///
/// A popular Dijsktra's [shunting-yard algorithm] converts
/// infix to postfix notation (RPN) in a linear time O(n). It
/// pushes numbers and constants to the output, while using
/// a stack to store temporary operands until they are needed
/// to be pushed to the output as some other operator with smaller
/// precedence is found.
///
/// # Errors
///
/// An `EmptyExpression` error is returned when tokens represent
/// no meaningful expression (no tokens or just brackets).
///
/// ```
/// # use xxcalc::parser::Parser;
/// # use xxcalc::{Tokens, TokensProcessor, ParsingError};
/// let mut parser = Parser::default();
///
/// let tokenized = &Tokens::new(None);
/// assert_eq!(parser.process(tokenized).unwrap_err(), ParsingError::EmptyExpression);
/// ```
///
/// A `MissingBracket` error is returned when brackets are unbalanced,
/// no matter if they were used to mark subexpression or an argument
/// list.
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::Parser;
/// # use xxcalc::{StringProcessor, TokensProcessor, ParsingError};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
///
/// {
///   let tokenized = tokenizer.process("(2");
///   assert_eq!(parser.process(tokenized).unwrap_err(), ParsingError::MissingBracket(0));
/// }
///
/// {
///   let tokenized = tokenizer.process("2)");
///   assert_eq!(parser.process(tokenized).unwrap_err(), ParsingError::MissingBracket(1));
/// }
///
/// {
///   let tokenized = tokenizer.process("foo(2, (2), -1");
///   assert_eq!(parser.process(tokenized).unwrap_err(), ParsingError::MissingBracket(3));
/// }
/// ```
///
/// An `UnexpectedToken` error is returned when parser encounters a token
/// with no meaning to the algorithm (such as `Token::Unknown`).
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::Parser;
/// # use xxcalc::{StringProcessor, TokensProcessor, ParsingError, Token};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
///
/// // note that @ is not a valid operator, so it results in Token::Unknown
/// let tokenized = tokenizer.process("(2)@2");
/// assert_eq!(parser.process(tokenized).unwrap_err(), ParsingError::UnexpectedToken(Token::Unknown('@'), 3));
/// ```
///
/// An `UnknownOperator` error is returned when a parser encounters an operator
/// token, but this operator is not registerd with the parser.
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::Parser;
/// # use xxcalc::{StringProcessor, TokensProcessor, ParsingError};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
///
/// let tokenized = tokenizer.process("(2)+2");
/// assert_eq!(parser.process(tokenized).unwrap_err(), ParsingError::UnknownOperator('+', 3));
/// ```
///
/// [shunting-yard algorithm]: https://en.wikipedia.org/wiki/Shunting-yard_algorithm
impl TokensProcessor for Parser {
  fn process(&mut self, tokens: &Tokens) -> Result<&Tokens, ParsingError> {
    let mut stack = TokenList::with_capacity(4);
    let mut iter = tokens.tokens.iter().peekable();

    self.output.clear();
    self.output.identifiers = tokens.identifiers.clone();

    while let Some(&(position, ref token)) = iter.next() {
      match *token {
        Token::Number(_) => self.output.push(position, token.to_owned()),
        Token::Identifier(_) => {
          if let Some(&&(_, Token::BracketOpening)) = iter.peek() {
            stack.push((position, token.to_owned()));
          } else {
            self.output.push(position, token.to_owned());
          }
        },
        Token::Operator(name) => {
          loop {
            match stack.last() {
              Some(&(_, Token::Operator(_))) | Some(&(_, Token::Identifier(_))) => {
                if self.lower_precedence(&token, &stack.last().unwrap().1) {
                  self.output.tokens.push(stack.pop().unwrap());
                } else {
                  break;
                }
              },
              _ => break
            }
          }

          if self.operators.contains_key(&name) {
            stack.push((position, token.to_owned()));
          } else {
            return Err(ParsingError::UnknownOperator(name, position));
          }
        },
        Token::BracketOpening => stack.push((position, token.to_owned())),
        Token::BracketClosing => {
          let mut found = false;

          loop {
            match stack.last() {
              Some(&(_, Token::BracketOpening)) => {
                found = true;
                stack.pop();
                break;
              },
              None => break,
              _ => self.output.tokens.push(stack.pop().unwrap())
            }
          }

          if !found {
            return Err(ParsingError::MissingBracket(position));
          }
        },
        Token::Separator => {
          loop {
            match stack.last() {
              Some(&(_, Token::BracketOpening)) => break,
              Some(_) => self.output.tokens.push(stack.pop().unwrap()),
              None => break
            }
          }
        },
        ref token => return Err(ParsingError::UnexpectedToken(token.to_owned(), position))
      }
    }

    loop {
      match stack.last() {
        Some(&(position, Token::BracketOpening)) => return Err(ParsingError::MissingBracket(position)),
        Some(_) => self.output.tokens.push(stack.pop().unwrap()),
        None => break
      }
    }

    if self.output.tokens.is_empty() {
      return Err(ParsingError::EmptyExpression);
    }

    Ok(&self.output)
  }
}

impl Parser {
  /// Creates an empty Parser with no defined operators.
  pub fn new() -> Parser {
    Parser {
      operators: BTreeMap::new(),
      output: Tokens::new(None)
    }
  }

  /// Registers operator identified by given name to the parser.
  ///
  /// Each operator must be registered and associated with its
  /// precedence and associative to make parser capable of valid
  /// RPN transformation. As operators always require two arguments,
  /// no arity is needed.
  ///
  /// If an operator with given name was already registered, it
  /// previous specification is returned.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::tokenizer::Tokenizer;
  /// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
  /// # use xxcalc::{Token, StringProcessor, TokensProcessor};
  /// let mut tokenizer = Tokenizer::default();
  /// let mut parser = Parser::default();
  ///
  /// let r = parser.register_operator('+', Operator::new(42, OperatorAssociativity::Left));
  /// assert!(r.is_none());
  ///
  /// let r = parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
  /// assert_eq!(r.unwrap(), Operator::new(42, OperatorAssociativity::Left));
  ///
  /// ```
  pub fn register_operator(&mut self, name: char, operator: Operator) -> Option<Operator> {
    self.operators.insert(name, operator)
  }

  #[inline(always)]
  fn lower_precedence(&self, a: &Token, b: &Token) -> bool {
    let &Operator(a_prec, ref a_assoc) = match *a {
      Token::Operator(name) => self.operators.get(&name).unwrap(),
      Token::Identifier(_) => return false,
      _ => unreachable!()
    };

    let &Operator(b_prec, _) = match *b {
      Token::Operator(name) => self.operators.get(&name).unwrap(),
      Token::Identifier(_) => return true,
      _ => unreachable!()
    };

    (*a_assoc == OperatorAssociativity::Left && a_prec <= b_prec) ||
    (*a_assoc == OperatorAssociativity::Right && a_prec < b_prec)
  }
}

#[cfg(test)]
mod tests {
  use TokensProcessor;
  use StringProcessor;
  use Token;
  use ParsingError;
  use parser::*;
  use tokenizer::*;

  #[test]
  fn test_operator_registration() {
    let mut parser = Parser::new();

    assert_eq!(parser.process(tokenize_ref!("2=2")).unwrap_err(), ParsingError::UnknownOperator('=', 1));

    parser.register_operator('=', Operator(-1, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("2=2")).unwrap().tokens.last().unwrap(), &(1, Token::Operator('=')));
  }

  #[test]
  fn test_precedence_and_associativity() {
    let mut parser = Parser::new();

    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('-', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));
    parser.register_operator('/', Operator(5, OperatorAssociativity::Left));
    parser.register_operator('^', Operator(10, OperatorAssociativity::Right));

    assert_eq!(parser.process(tokenize_ref!("2+2*2")).unwrap().tokens.last().unwrap(), &(1, Token::Operator('+')));
    assert_eq!(parser.process(tokenize_ref!("2*2+2")).unwrap().tokens.last().unwrap(), &(3, Token::Operator('+')));
    assert_eq!(parser.process(tokenize_ref!("2*2/2")).unwrap().tokens.last().unwrap(), &(3, Token::Operator('/')));
    assert_eq!(parser.process(tokenize_ref!("2/2*2")).unwrap().tokens.last().unwrap(), &(3, Token::Operator('*')));
    assert_eq!(parser.process(tokenize_ref!("2*2^2")).unwrap().tokens.last().unwrap(), &(1, Token::Operator('*')));
    assert_eq!(parser.process(tokenize_ref!("2^2*2")).unwrap().tokens.last().unwrap(), &(3, Token::Operator('*')));

    assert_eq!(parser.process(tokenize_ref!("2+2+2")).unwrap().tokens.iter().rev().skip(1).next().unwrap(), &(4, Token::Number(2.0)));
    assert_eq!(parser.process(tokenize_ref!("2^2^2")).unwrap().tokens.iter().rev().skip(1).next().unwrap(), &(3, Token::Operator('^')));
  }

  #[test]
  fn test_symbols() {
    let mut parser = Parser::new();
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("x")).unwrap().tokens.first().unwrap(), &(0, Token::Identifier(0)));
    assert_eq!(parser.process(tokenize_ref!("foobar")).unwrap().tokens.first().unwrap(), &(0, Token::Identifier(0)));

    assert_eq!(parser.process(tokenize_ref!("2x")).unwrap().tokens.len(), 3);
    assert_eq!(parser.process(tokenize_ref!("2x")).unwrap().tokens.last().unwrap(), &(0, Token::Operator('*')));
  }

  #[test]
  fn test_brackets() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("2+2*2")).unwrap().tokens.last().unwrap(), &(1, Token::Operator('+')));
    assert_eq!(parser.process(tokenize_ref!("(2+2)*2")).unwrap().tokens.last().unwrap(), &(5, Token::Operator('*')));

    assert_eq!(parser.process(tokenize_ref!("2(14+2)")).unwrap().tokens.last().unwrap(), &(0, Token::Operator('*')));

    assert_eq!(parser.process(tokenize_ref!("(((2)))")).unwrap().tokens.first().unwrap(), &(3, Token::Number(2.0)));
    assert_eq!(parser.process(tokenize_ref!("(((2))+2)")).unwrap().tokens.last().unwrap(), &(6, Token::Operator('+')));
  }

  #[test]
  fn test_missing_brackets() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("2+(2(2+2)")).unwrap_err(), ParsingError::MissingBracket(2));
    assert_eq!(parser.process(tokenize_ref!("(2(2+2)")).unwrap_err(), ParsingError::MissingBracket(0));
    assert_eq!(parser.process(tokenize_ref!("2(2+2))")).unwrap_err(), ParsingError::MissingBracket(6));
  }

  #[test]
  fn test_empty_expression() {
    let mut parser = Parser::new();

    assert_eq!(parser.process(tokenize_ref!("")).unwrap_err(), ParsingError::EmptyExpression);
    assert_eq!(parser.process(tokenize_ref!("((()))")).unwrap_err(), ParsingError::EmptyExpression);
  }

  #[test]
  fn test_unknown_tokens() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("@2")).unwrap_err(), ParsingError::UnexpectedToken(Token::Unknown('@'), 0));
    assert_eq!(parser.process(tokenize_ref!("2+2*{2+2}")).unwrap_err(), ParsingError::UnexpectedToken(Token::Unknown('{'), 4));
  }

  #[test]
  fn test_arguments() {
    let mut parser = Parser::new();

    assert_eq!(parser.process(tokenize_ref!("foo()")).unwrap().tokens.len(), 1);
    assert_eq!(parser.process(tokenize_ref!("foo(1)")).unwrap().tokens.len(), 2);
    assert_eq!(parser.process(tokenize_ref!("foo(1, 2)")).unwrap().tokens.len(), 3);
    assert_eq!(parser.process(tokenize_ref!("foo(1, 2)")).unwrap().tokens.last().unwrap(), &(0, Token::Identifier(0)));
    assert_eq!(parser.process(tokenize_ref!("foo(-1, 2)")).unwrap().tokens.first().unwrap(), &(4, Token::Number(-1.0)));
  }
}
