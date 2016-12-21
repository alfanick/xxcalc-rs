//! `Evaluator` is a `TokensReducer`, it takes token in RPN form
//! and evaluates its Polynomial value.

use super::*;
use polynomial::{Polynomial, PolynomialError};
use std::collections::BTreeMap;
use std::fmt;

/// Pointer to function processing `Polynomial` arguments.
///
/// Such function takes a defined number of Polynomial
/// arguments and transform them into a single Polynomial
/// value. It is used to implement operators and other
/// functions in the evaluator.
pub type FunctionHandle = Box<Fn(Vec<Polynomial>) -> Result<Polynomial, EvaluationError>>;

/// Definition of function with its arity.
///
/// A function is used to implement operators and other
/// functions in the evaluator. Each function consist
/// of `FunctionHandle` which process arguments into a single
/// `Polynomial` value.
///
/// A function handle is guaranteed to receive a defined
/// number of arguments, as this is checked during the
/// evaluation (there is no need checking arity of arguments
/// in the handler).
pub struct Function {
  arity: usize,
  handle: FunctionHandle
}

/// Debug formatter for `Function`
impl fmt::Debug for Function {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Function(arity: {}, handle: ?)", self.arity)
  }
}

impl Function {
  /// Creates a new function with given arity and handler.
  ///
  /// Handler can be a pointer to a closure or a function.
  /// A function handler is guaranteed to receive required
  /// number of arguments when called.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial_calculator::functions;
  /// # use xxcalc::evaluator::Function;
  /// # use xxcalc::polynomial::Polynomial;
  /// let f_a = Function::new(2, Box::new(functions::addition));
  /// let f_b = Function::new(0, Box::new(|args| {
  ///   return Ok(Polynomial::constant(42.0));
  /// }));
  /// ```
  pub fn new(a: usize, h: FunctionHandle) -> Function {
    Function {
      arity: a,
      handle: h
    }
  }
}

/// Evaluator takes `Tokens` in Reverse Polish Notation and evaluates
/// them using defined functions and constants into a sngle Polynomial
/// value.
///
/// Evaluator stores registered functions (with their arity) between
/// multiple executions. There is no difference between an operator
/// and a function call. Additionaly constants can be registered.
/// Both identifiers are kept in binary tree, so their retrieval
/// is relatively quick. Symbols used for functions or constants
/// must be unique, a function with no arguments can replace a
/// constant, however its value may change.
///
/// # Examples
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
/// # use xxcalc::evaluator::{Evaluator, Function};
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
/// let mut evaluator = Evaluator::default();
///
/// parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
/// evaluator.register_function("+", Function::new(2, Box::new(|args| {
///   // not a production code, just a sample
///   Ok(args[0].clone() + args[1].clone())
/// })));
///
/// let parsed = parser.process(tokenizer.process("2+2")).unwrap();
/// assert_eq!(evaluator.process(parsed), Ok(Polynomial::constant(4.0)));
/// ```
///
/// # Extending
///
/// One can directly register functions or constants with the evaluator,
/// or embed the evalutor in another `TokensReducer` which will add these
/// handlers by default.
pub struct Evaluator {
  functions: BTreeMap<String, Function>,
  constants: BTreeMap<String, Polynomial>
}

/// Creates a new default Evaluator.
///
/// Such evaluator is not aware of any functions or constants.
/// One must define functions before being able to evaluate
/// operators or other calls.
impl Default for Evaluator {
  fn default() -> Evaluator {
    Evaluator::new()
  }
}

/// This is a main processing unit in the evaluator. It takes
/// tokens in Reverse Polish Notation and evaluates them into
/// a single `Polynomial` value.
///
/// Before evaluating functions, operators or constants they
/// must be registered, as evaluator has no knowledge what to
/// do with the arguments and how to reduce them into a single
/// value. Operators and functions are actualy the same thing,
/// except that operators always require two arguments.
///
/// A traditional stack based postfix evaluation algorithm is
/// used (it computes the result in a linear time). Numbers and
/// constants are put on a stack, until a operator or a function
/// call is required. Such call takes off appropriate number of
/// arguments from the stack and calls the function handler
/// with these arguments. Result of such evaluation is put back
/// on the stack. In the end last value on the stack is returned
/// as the result of the evaluation.
///
/// # Errors
///
/// A `PolynomialError` is returned when underlying function handler returns
/// an error (it may happen as a result of converting non constant to float,
/// division by zero of polynomials or division of polynomials with wrong
/// degree).
///
/// A `MultipleExpressions` error is returned when there are multiple tokens
/// left on the stack. It is causes by providing to many arguments to a
/// function or giving too many expressions.
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
/// # use xxcalc::evaluator::{Evaluator, Function};
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
/// let mut evaluator = Evaluator::default();
///
/// {
///   let parsed = parser.process(tokenizer.process("2, 2")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::MultipleExpressions);
/// }
///
/// evaluator.register_function("foo", Function::new(1, Box::new(|args| {
///   Ok(Polynomial::constant(42.0))
/// })));
///
/// {
///   let parsed = parser.process(tokenizer.process("foo(2, 2)")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::MultipleExpressions);
/// }
/// ```
///
/// An `ArgumentMissing` error is returned when number of tokens on a stack
/// is less than required arity of given functions. The error contains
/// required arity and position of error.
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
/// # use xxcalc::evaluator::{Evaluator, Function};
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
/// let mut evaluator = Evaluator::default();
///
/// parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
/// evaluator.register_function("+", Function::new(2, Box::new(|args| {
///   // not a production code, just a sample
///   Ok(args[0].clone() + args[1].clone())
/// })));
///
/// {
///   let parsed = parser.process(tokenizer.process("2+2+")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::ArgumentMissing(String::from("+"), 2, 3));
/// }
///
/// evaluator.register_function("foo", Function::new(1, Box::new(|args| {
///   Ok(Polynomial::constant(42.0))
/// })));
///
/// {
///   let parsed = parser.process(tokenizer.process("foo()")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::ArgumentMissing(String::from("foo"), 1, 0));
/// }
/// ```
///
/// An `UnknownSymbol` error is returned when an operator or identifier token is
/// encountered with a name of unregistered function or constant. Each operator,
/// function and constant need to be registered before it can be evaluated.
///
/// ```
/// # use xxcalc::tokenizer::Tokenizer;
/// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
/// # use xxcalc::evaluator::{Evaluator, Function};
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
/// let mut tokenizer = Tokenizer::default();
/// let mut parser = Parser::default();
/// let mut evaluator = Evaluator::default();
///
/// parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
///
/// {
///   let parsed = parser.process(tokenizer.process("2+2")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::UnknownSymbol(String::from("+"), 1));
/// }
///
/// {
///   let parsed = parser.process(tokenizer.process("foo(1)")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::UnknownSymbol(String::from("foo"), 0));
/// }
///
/// {
///   let parsed = parser.process(tokenizer.process("pi")).unwrap();
///   assert_eq!(evaluator.process(parsed).unwrap_err(), EvaluationError::UnknownSymbol(String::from("pi"), 0));
/// }
/// ```
impl TokensReducer for Evaluator {
  fn process(&self, tokens: &Tokens) -> Result<Polynomial, EvaluationError> {
    let mut stack: Vec<Polynomial> = Vec::with_capacity(10);

    for &(position, ref token) in &tokens.tokens {
      match *token {
        Token::Number(x) => stack.push(Polynomial::constant(x)),
        Token::Operator(x) => {
          let result = try!(self.call_function(&x.to_string(), position, &mut stack));
          stack.push(result);
        },
        Token::Identifier(idx) => {
          let x = tokens.identifiers.get(idx).unwrap();

          if let Some(constant) = self.constants.get(x) {
            stack.push(constant.clone());
            continue;
          }

          let result = try!(self.call_function(&x, position, &mut stack));
          stack.push(result);
        },
        _ => unreachable!()
      }
    }

    if stack.len() == 1 {
      Ok(stack.pop().unwrap())
    } else {
      Err(EvaluationError::MultipleExpressions)
    }
  }
}

impl Evaluator {
  /// Creates an empty Evaluator with no defined symbols.
  pub fn new() -> Evaluator {
    Evaluator {
      functions: BTreeMap::new(),
      constants: BTreeMap::new()
    }
  }

  /// Registers a function with its name.
  ///
  /// Each function (or an operator) must have a registered function
  /// handle which takes arguments (or operands) and evaluate them
  /// into a single value Polynomial.
  //
  /// If a function with the same name has been registered, previously
  /// registered function is returned, however the name of the function
  /// cannot collide with an already registered constant.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::tokenizer::Tokenizer;
  /// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
  /// # use xxcalc::evaluator::{Evaluator, Function};
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
  /// let mut tokenizer = Tokenizer::default();
  /// let mut parser = Parser::default();
  /// let mut evaluator = Evaluator::default();
  ///
  /// parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
  ///
  /// {
  ///   let parsed = parser.process(tokenizer.process("2+2")).unwrap();
  ///   assert_eq!(evaluator.process(parsed), Err(EvaluationError::UnknownSymbol(String::from("+"), 1)));
  /// }
  ///
  /// evaluator.register_function("+", Function::new(2, Box::new(|args| {
  ///   // not a production code, just a sample
  ///   Ok(args[0].clone() + args[1].clone())
  /// })));
  ///
  /// {
  ///   let parsed = parser.process(tokenizer.process("2+2")).unwrap();
  ///   assert_eq!(evaluator.process(parsed), Ok(Polynomial::constant(4.0)));
  /// }
  /// ```
  ///
  /// # Errors
  ///
  /// A ConflictingName error is returned when name of the function collides
  /// with previously registered constant.
  ///
  /// ```
  /// # use xxcalc::evaluator::{Evaluator, Function};
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
  /// let mut evaluator = Evaluator::default();
  ///
  /// evaluator.register_constant("foo", Polynomial::constant(42.0));
  /// let result = evaluator.register_function("foo", Function::new(1, Box::new(|args| {
  ///   Ok(args[0].clone())
  /// })));
  ///
  /// assert_eq!(result.unwrap_err(), EvaluationError::ConflictingName(String::from("foo")));
  /// ```
  pub fn register_function(&mut self, name: &str, function: Function) -> Result<Option<Function>, EvaluationError> {
    if let Some(_) = self.constants.get(name) {
      return Err(EvaluationError::ConflictingName(name.to_string()));
    }

    Ok(self.functions.insert(name.to_string(), function))
  }

  /// Registers a Polynomial constant with its name.
  ///
  /// An identifier with given name is replaced with the constant value
  /// when it is encountered during evaluation process.
  //
  /// If a constant with the same name has been registered, previously
  /// registered constant is returned, however the name of the constant
  /// cannot collide with an already registered function.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::tokenizer::Tokenizer;
  /// # use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
  /// # use xxcalc::evaluator::{Evaluator, Function};
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
  /// let mut tokenizer = Tokenizer::default();
  /// let mut parser = Parser::default();
  /// let mut evaluator = Evaluator::default();
  ///
  /// {
  ///   let parsed = parser.process(tokenizer.process("foo")).unwrap();
  ///   assert_eq!(evaluator.process(parsed), Err(EvaluationError::UnknownSymbol(String::from("foo"), 0)));
  /// }
  ///
  /// evaluator.register_constant("foo", Polynomial::constant(42.0));
  ///
  /// {
  ///   let parsed = parser.process(tokenizer.process("foo")).unwrap();
  ///   assert_eq!(evaluator.process(parsed), Ok(Polynomial::constant(42.0)));
  /// }
  /// ```
  ///
  /// # Errors
  ///
  /// A ConflictingName error is returned when name of the constant collides
  /// with previously registered function.
  ///
  /// ```
  /// # use xxcalc::evaluator::{Evaluator, Function};
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::{StringProcessor, TokensProcessor, TokensReducer, EvaluationError};
  /// let mut evaluator = Evaluator::default();
  ///
  /// evaluator.register_function("foo", Function::new(1, Box::new(|args| {
  ///   Ok(args[0].clone())
  /// })));
  /// let result = evaluator.register_constant("foo", Polynomial::constant(42.0));
  ///
  /// assert_eq!(result.unwrap_err(), EvaluationError::ConflictingName(String::from("foo")));
  /// ```
  pub fn register_constant(&mut self, name: &str, constant: Polynomial) -> Result<Option<Polynomial>, EvaluationError> {
    if let Some(_) = self.functions.get(name) {
      return Err(EvaluationError::ConflictingName(name.to_string()));
    }

    Ok(self.constants.insert(name.to_string(), constant))
  }

  #[inline(always)]
  fn call_function(&self, name: &str, position: usize, stack: &mut Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    if let Some(function) = self.functions.get(name) {
      if stack.len() < function.arity {
        Err(EvaluationError::ArgumentMissing(name.to_owned(), function.arity, position))
      } else {
        let stack_len = stack.len();
        let args: Vec<Polynomial> = stack.split_off(stack_len - function.arity);

        (function.handle)(args)
      }
    } else {
      Err(EvaluationError::UnknownSymbol(name.to_owned(), position))
    }
  }
}

/// Encloses `PolynomialError` into an `EvaluationError`
impl From<PolynomialError> for EvaluationError {
  fn from(e: PolynomialError) -> EvaluationError {
    EvaluationError::PolynomialError(e)
  }
}

#[cfg(test)]
#[allow(unused_must_use)]
mod tests {
  use TokensReducer;
  use TokensProcessor;
  use StringProcessor;
  use EvaluationError;
  use evaluator::{Evaluator, Function};
  use parser::{Parser, Operator, OperatorAssociativity};
  use tokenizer::*;
  use polynomial::*;

  #[test]
  fn test_symbol_registration() {
    let mut evaluator = Evaluator::new();

    assert!(evaluator.register_constant("foo", Polynomial::constant(1.0)).is_ok());
    assert!(evaluator.register_constant("foo", Polynomial::constant(2.0)).is_ok());

    assert!(evaluator.register_function("foo", Function::new(1, Box::new(|_| Err(EvaluationError::MultipleExpressions)))).is_err());
    assert!(evaluator.register_function("bar", Function::new(1, Box::new(|_| Err(EvaluationError::MultipleExpressions)))).is_ok());

    assert!(evaluator.register_constant("bar", Polynomial::constant(3.0)).is_err());

  }

  pub fn addition(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() + args[1].clone())
  }

  pub fn subtraction(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() - args[1].clone())
  }

  pub fn multiplication(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() * args[1].clone())
  }

  #[test]
  fn test_operators() {
    let mut evaluator = Evaluator::new();
    let mut parser = Parser::new();

    parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    evaluator.register_function("+", Function::new(2, Box::new(addition)));
    parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));
    evaluator.register_function("-", Function::new(2, Box::new(subtraction)));
    parser.register_operator('*', Operator::new(5, OperatorAssociativity::Left));
    evaluator.register_function("*", Function::new(2, Box::new(multiplication)));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2+4")).unwrap()), Ok(Polynomial::constant(6.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2*4")).unwrap()), Ok(Polynomial::constant(8.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2+4*6")).unwrap()), Ok(Polynomial::constant(26.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2*4+6")).unwrap()), Ok(Polynomial::constant(14.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("(2+4)*6")).unwrap()), Ok(Polynomial::constant(36.0)));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2+-4")).unwrap()), Ok(Polynomial::constant(-2.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2--4")).unwrap()), Ok(Polynomial::constant(6.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2++4")).unwrap()), Ok(Polynomial::constant(6.0)));
  }

  #[test]
  fn test_constants() {
    let mut evaluator = Evaluator::new();
    let mut parser = Parser::new();

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("foo")).unwrap()), Err(EvaluationError::UnknownSymbol("foo".to_string(), 0)));

    evaluator.register_constant("foo", Polynomial::constant(123.0));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("foo")).unwrap()), Ok(Polynomial::constant(123.0)));
  }

  #[test]
  fn test_functions() {
    let mut evaluator = Evaluator::new();
    let mut parser = Parser::new();

    parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    evaluator.register_function("+", Function::new(2, Box::new(addition)));
    parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));
    evaluator.register_function("-", Function::new(2, Box::new(subtraction)));
    parser.register_operator('*', Operator::new(5, OperatorAssociativity::Left));
    evaluator.register_function("*", Function::new(2, Box::new(multiplication)));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("double(2)")).unwrap()), Err(EvaluationError::UnknownSymbol("double".to_string(), 0)));

    evaluator.register_function("double", Function::new(1, Box::new(|args|{
      Ok(args[0].clone() * Polynomial::constant(2.0))
    })));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("double(2)")).unwrap()), Ok(Polynomial::constant(4.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("double(4*-0.5)")).unwrap()), Ok(Polynomial::constant(-4.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("double()")).unwrap()), Err(EvaluationError::ArgumentMissing("double".to_string(), 1, 0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("double(1, 2)")).unwrap()), Err(EvaluationError::MultipleExpressions));
  }

  #[test]
  fn test_functions_no_arguments() {
    let mut evaluator = Evaluator::new();
    let mut parser = Parser::new();

    parser.register_operator('*', Operator::new(5, OperatorAssociativity::Left));
    evaluator.register_function("*", Function::new(2, Box::new(multiplication)));

    evaluator.register_function("unit", Function::new(0, Box::new(|_|{
      Ok(Polynomial::constant(1.0))
    })));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("unit()")).unwrap()), Ok(Polynomial::constant(1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("unit")).unwrap()), Ok(Polynomial::constant(1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("unit*2")).unwrap()), Ok(Polynomial::constant(2.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2unit")).unwrap()), Ok(Polynomial::constant(2.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("unit(2)")).unwrap()), Err(EvaluationError::MultipleExpressions));
  }

  #[test]
  fn test_functions_multiple_arguments() {
    let mut evaluator = Evaluator::new();
    let mut parser = Parser::new();

    parser.register_operator('*', Operator::new(5, OperatorAssociativity::Left));
    evaluator.register_function("*", Function::new(2, Box::new(multiplication)));

    evaluator.register_function("mod", Function::new(2, Box::new(|args|{
      Ok(Polynomial::constant(try!(args[0].clone().as_f64()) % try!(args[1].clone().as_f64())))
    })));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("mod(17, 4)")).unwrap()), Ok(Polynomial::constant(1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("mod(1)")).unwrap()), Err(EvaluationError::ArgumentMissing("mod".to_string(), 2, 0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("mod(1, 2, 3)")).unwrap()), Err(EvaluationError::MultipleExpressions));
  }

  #[test]
  fn test_multiple_expression() {
    let evaluator = Evaluator::new();
    let mut parser = Parser::new();

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("2, 2")).unwrap()), Err(EvaluationError::MultipleExpressions));
  }

  #[test]
  fn test_polynomials() {
    let mut evaluator = Evaluator::new();
    let mut parser = Parser::new();

    parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    evaluator.register_function("+", Function::new(2, Box::new(addition)));
    parser.register_operator('*', Operator::new(5, OperatorAssociativity::Left));
    evaluator.register_function("*", Function::new(2, Box::new(multiplication)));

    evaluator.register_constant("x", Polynomial::linear(0.0, 1.0));

    assert_eq!(evaluator.process(parser.process(tokenize_ref!("x")).unwrap()), Ok(Polynomial::linear(0.0, 1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("x*x")).unwrap()), Ok(Polynomial::new(&[0.0, 0.0, 1.0])));
    assert_eq!(evaluator.process(parser.process(tokenize_ref!("x+x")).unwrap()), evaluator.process(parser.process(tokenize_ref!("2x")).unwrap()));
  }
}
