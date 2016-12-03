//! foo bar
pub mod polynomial;
#[macro_use]
pub mod tokenizer;
pub mod parser;
pub mod evaluator;
pub mod calculator;
pub mod polynomial_calculator;
pub mod linear_solver;

use std::ops::Index;
use std::collections::BTreeMap;

/// Token is a basic unit returned after tokenization using
/// a StringProcessor.
///
/// Token can be than rearranged with a TokensProcessor and
/// interpreted (evaluated) to a Polynomial using a TokensReducer.
///
/// Tokens are used to conveniently store expressions in partially
/// parsed and computer readable form.
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
  /// Opening bracket `(` or beginning of subexpression
  BracketOpening,
  /// Closing bracket `)` or ending of subexpression
  BracketClosing,
  /// Argument separator
  Separator,
  /// Floating point number
  Number(f64),
  /// Single character operator
  Operator(char),
  /// Symbol identifier (represented by index in identifiers table)
  Identifier(usize),
  /// Unidentified character (with no meaning to a StringProcessor)
  Unknown(char),
  /// Skip marker
  Skip
}

/// List of tokens with their position.
///
/// Tokens are represented as space-efficient continous vector
/// of tuples consisting of position in a input string and a
/// corresponding Token.
pub type TokenList = Vec<(usize, Token)>;

/// Vector of unique identifiers.
///
/// Token::Identifier stores just a location in this vector,
/// this keeps size of individual tokens minimal.
pub type Identifiers = Vec<String>;

/// Tokens is a compound storage for list of tokens with
/// their identifiers.
///
/// A TokenList is invalid without Identifiers, therefore
/// this struct keeps them always together. Furthermore
/// a lookup table is kept, so creating new identifier is
/// a relatively quick task.
#[derive(Debug)]
pub struct Tokens {
  /// List of tokens
  pub tokens: TokenList,
  /// Identifier strings used in Token::Identifier
  pub identifiers: Identifiers,
  lookup: BTreeMap<String, usize>
}

/// Transforms text expression into list of tokens.
///
/// A StringProcessor can be implemented for a tokenizer (lexer)
/// which converts some text expression into a list of tokens.
pub trait StringProcessor {
  fn process(self: &mut Self, line: &str) -> &Tokens;
}

/// Transforms list of tokens into another list of tokens.
///
/// A TokensProcessor can be implemented for a parser which
/// takes a list of tokens in some order and transform them
/// into list of tokens in the other form (like infix to
/// RPN notation). Furthermore a TokensProcessor can be used
/// to extend tokenizer with knowledge of new tokens, as it
/// can transform unknown tokens to known ones.
pub trait TokensProcessor {
  fn process(&mut self, tokens: &Tokens) -> Result<&Tokens, ParsingError>;
}

/// Evaluates list of tokens into a single Polynomial value.
///
/// A TokensReducer takes a list of tokens in some expected
/// arrangement and evaluates them into a single Polynomial
/// value. It can be used for implementation of various
/// computational languages (such as the scientific calcualtor).
pub trait TokensReducer {
  fn process(&self, tokens: &Tokens) -> Result<polynomial::Polynomial, EvaluationError>;
}

/// Returns position and token with given index.
///
/// One should note that token position is indepentent
/// from its index.
///
/// # Panics
///
/// It will panic when the index is greater than number of
/// tokens stored in the list.
///
/// # Examples
///
/// ```
/// # use xxcalc::{Tokens, Token};
/// let mut tokens = Tokens::new(None);
///
/// tokens.push(0, Token::Number(1.0));
/// tokens.push(8, Token::Number(2.0));
///
/// assert_eq!(tokens[0], (0, Token::Number(1.0)));
/// assert_eq!(tokens[1], (8, Token::Number(2.0)));
/// ```
impl Index<usize> for Tokens {
  type Output = (usize, Token);

  fn index(&self, idx: usize) -> &(usize, Token) {
    &self.tokens[idx]
  }
}

impl Tokens {
  /// Creates a new token storage with optional capacity of
  /// identifiers.
  pub fn new(i_cap: Option<usize>) -> Tokens {
    Tokens {
      tokens: TokenList::with_capacity(10),
      identifiers: Identifiers::with_capacity(i_cap.unwrap_or(0)),
      lookup: BTreeMap::new()
    }
  }

  /// Clears tokens list, however underlying identifiers vector and
  /// its lookup cache is not cleared, as identifiers may be reused.
  #[inline(always)]
  pub fn clear(&mut self) {
    self.tokens.clear()
  }

  /// Pushes a token (with its position) to the end of token list.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::{Tokens, Token};
  /// let mut tokens = Tokens::new(None);
  ///
  /// tokens.push(0, Token::Number(1.0));
  /// assert_eq!(tokens.tokens.len(), 1);
  ///
  /// tokens.push(1, Token::Number(2.0));
  /// assert_eq!(tokens.tokens.len(), 2);
  /// ```
  #[inline(always)]
  pub fn push(&mut self, position: usize, token: Token) {
    self.tokens.push((position, token))
  }

  /// Pushes a identifier (with its position) to the end of token list.
  ///
  /// Using a lookup cache, an offset in identifier table is obtained.
  /// If identifier does not yet exist, it is added both to the identifier
  /// vector and to the lookup cache. Identifiers are case-agnostic.
  /// A Token::Identifier with appropriate offset is pushed to the end
  /// of the token list.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::{Tokens, Token};
  /// let mut tokens = Tokens::new(None);
  ///
  /// tokens.push_identifier(0, &String::from("FOO"));
  /// assert_eq!(tokens[0], (0, Token::Identifier(0)));
  /// tokens.push_identifier(4, &String::from("foo"));
  /// assert_eq!(tokens[1], (4, Token::Identifier(0)));
  /// tokens.push_identifier(8, &String::from("bar"));
  /// assert_eq!(tokens[2], (8, Token::Identifier(1)));
  /// assert_eq!(tokens.identifiers, ["foo", "bar"]);
  /// ```
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
        self.identifiers.push(value.to_lowercase());
        self.identifiers.len() - 1
      }
    };
    self.push(position, Token::Identifier(idx));
  }
}

/// An error that occurs during token processing,
/// usually by a parser.
#[derive(Debug, PartialEq)]
pub enum ParsingError {
  /// Encountered an operator which is not recognized by a parser.
  /// The operator is a first argument, while its position is the last one.
  UnknownOperator(char, usize),

  /// Encountered a Token with no meaning to the parser,
  /// probably a Token::Unknown. This token is a first argument, while its
  /// position is the last one.
  UnexpectedToken(Token, usize),

  /// Detected a missing opening or closing bracket at given position.
  MissingBracket(usize),

  /// Provided token list is empty, where expected it shouldn't be so.
  EmptyExpression
}

/// An error that occurs during token reduction,
/// usually by an evaluator.
#[derive(Debug, PartialEq)]
pub enum EvaluationError {
  /// Encountered an operator, a constant or a function with no meaning
  /// to the evaluator. Most probably such symbol must be registered
  /// beforehand. The identifier is a first argument, while its position
  /// is the last one.
  UnknownSymbol(String, usize),

  /// Number of provided arguments for a function or an operator are not
  /// enough (the function is registered with larger arity). The symbol
  /// is a first argument, expected arity is a second argument, while the
  /// position is the last one.
  ArgumentMissing(String, usize, usize),

  /// Multiple expressions where encountered, where not expected (as in
  /// too many arguments or too many complete expressions).
  MultipleExpressions,

  /// A symbol with given name is conflicting with already registered
  /// function or constant.
  ConflictingName(String),

  /// Wraps polynomial error which could be encountered during the evaluation
  /// as result of some mathematical operation.
  PolynomialError(polynomial::PolynomialError),

  /// Wraps linear solver error which could be encountered when assumptions
  /// needed for solving are not met.
  SolvingError(linear_solver::SolvingError),

  /// Used when exponent is of greater degree than zero. Result of such
  /// exponentiation would not be a polynomial anylonger.
  NonConstantExponent,

  /// Used when exponent is not a natural number, while the base of
  /// exponentiation is not a constant. Result of such operations would
  /// not be a polynomial anylonger.
  NonNaturalExponent
}