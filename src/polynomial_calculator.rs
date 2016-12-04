//! Defines a PolynomialCalculator with common arithmetic operations, functions
//! and constants already defined.
//!
//! It supports various arithmetical operations, functions and some constants by
//! default. Operators such as addition `+`, subtraction `-`, multiplication `*`,
//! division `/` and exponentiation `^` are available on polynomials. Please note
//! that a simple floating point numbers (represented using double `f64` type) are
//! supported as well, as these are special case of a polynomial (a constant
//! polynomial of a degree zero).
//!
//! Furthermore functions such as arbitrary base logarithm `log(number, base)`,
//! decimal logarithm `log10(number)` and evaluation of the polynomial
//! `bind(polynomial, number)` are provided by default too. Symbols such as `inf`,
//! `nan`, `pi` and `e` are defined too.
//!
//! In order to write polynomials the `x` symbol must be used (which internally
//! is a constant defining a polynomial with coefficient one for the power of one).
//!
//! In order to make the polynomial calculator reusable it is split into two
//! functional units: a PolynomialParser and a PolynomialEvaluator. A PolynomialParser,
//! extends basic infix parser with knowledge of basic arithmetic operators (`+`, `-`,
//! `*`, `/`, `^`) with correct precedence (priority) and associativity. One can use
//! this parser to implement the other ones. Then, a PolynomialEvaluator is defined,
//! which extends a basic RPN evaluator with functions handling these operators and
//! handlers for `log`, `log10` and `bind` functions, as well as the common constants.
//!
//! The function handlers are available in the public module, so one can reuse them
//! when implementing a custom evaluator. These handlers try to do operations in-place
//! where possible, as a result no additional instances of Polynomial are created.
//!
//! # Examples
//!
//! A PolynomialCalculator provides an easy way to integrate the calculator into
//! your project. It simply takes a string expression and returns evaluated value.
//!
//! ```
//! use xxcalc::polynomial_calculator::PolynomialCalculator;
//! use xxcalc::calculator::Calculator;
//! use xxcalc::polynomial::Polynomial;
//!
//! assert_eq!(PolynomialCalculator.process("(2+2)*-2"), Ok(Polynomial::constant(-8.0)));
//! assert_eq!(PolynomialCalculator.process("(2+2)*-2").unwrap().as_f64().unwrap(), -8.0);
//! assert_eq!(String::from(PolynomialCalculator.process("(x+1)*(-0.13x^18-x^7)").unwrap()), "-0.13x^19-0.13x^18-x^8-x^7");
//! ```
//!
//! However, the highest performance can be obtained by using a tokenizer, parser and
//! evaluator directly. A PolynomialCalculator creates a new instance of these for each
//! evaluation, which wastes buffers and requires multiple allocations from the operating
//! system.
//!
//! ```
//! use xxcalc::tokenizer::Tokenizer;
//! use xxcalc::polynomial_calculator::{PolynomialParser, PolynomialEvaluator};
//! use xxcalc::{StringProcessor, TokensProcessor, TokensReducer};
//! use xxcalc::polynomial::Polynomial;
//!
//! let mut tokenizer = Tokenizer::default();
//! let mut parser = PolynomialParser::default();
//! let evaluator = PolynomialEvaluator::default();
//!
//! // process some input
//! for _ in 0..10 {
//!   let tokenized = tokenizer.process("(2+2)*-2");
//!   let parsed = parser.process(tokenized);
//!   assert_eq!(evaluator.process(parsed.unwrap()), Ok(Polynomial::constant(-8.0)));
//! }
//! ```

use super::*;
use calculator::*;
use tokenizer::Tokenizer;
use evaluator::{Evaluator, Function};
use parser::{Parser, Operator, OperatorAssociativity};
use polynomial::Polynomial;
use std::f64::consts::{PI, E};

/// PolynomialCalculator is a calculator using a PolynomialParser and a PolynomialEvaluator
/// to provide multiple default operations.
///
/// This calculator supports addition `+`, subtraction `-`, multiplication `*`,
/// division `/` and exponentiation `^` operators, `log(number, base)`,
/// `log10(number)` and `bind(polynomial, double)` functions, `x`, `inf`, `nan`
/// symbols and `pi` and `e` constants.
///
/// While usage of the calculator is the easiest way of embedding computation
/// engine into your program, please note that a Tokenizer, PolynomialParser and
/// PolynomialEvaluator is created with each call, which requires reallocation
/// of memory.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial_calculator::PolynomialCalculator;
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::calculator::Calculator;
/// # use std::f64::consts::PI;
/// assert_eq!(PolynomialCalculator.process("2+2"), Ok(Polynomial::constant(4.0)));
/// assert_eq!(PolynomialCalculator.process("(2+2)*-2"), Ok(Polynomial::constant(-8.0)));
/// assert_eq!(String::from(PolynomialCalculator.process("(x+1)*(-0.13x^18-x^7)").unwrap()), "-0.13x^19-0.13x^18-x^8-x^7");
/// assert_eq!(PolynomialCalculator.process("bind(pi*x^2, 10)"), Ok(Polynomial::constant(PI * 10.0 * 10.0)));
/// ```
pub struct PolynomialCalculator;

impl Calculator<Tokenizer, PolynomialParser, PolynomialEvaluator> for PolynomialCalculator {

}

/// Extends Evaluator with handlers for common operators and functions.
pub struct PolynomialEvaluator {
  /// Underlying evaluator (one can use it to extend it furthermore)
  pub evaluator: Evaluator
}

/// Creates PolynomialEvaluator and extends the basic Evaluator.
///
/// Handlers for common arithmetic operations, functions and some constants
/// are registered to the underlying evaluator.
impl Default for PolynomialEvaluator {
  fn default() -> PolynomialEvaluator {
    let mut evaluator = Evaluator::default();

    evaluator.register_constant("x", Polynomial::linear(0.0, 1.0)).unwrap();
    evaluator.register_constant("pi", Polynomial::constant(PI)).unwrap();
    evaluator.register_constant("e", Polynomial::constant(E)).unwrap();
    evaluator.register_constant("inf", Polynomial::constant(1.0f64 / 0.0f64)).unwrap();
    evaluator.register_constant("nan", Polynomial::constant(0.0f64 / 0.0f64)).unwrap();

    evaluator.register_function("+", Function::new(2, Box::new(functions::addition))).unwrap();
    evaluator.register_function("-", Function::new(2, Box::new(functions::subtraction))).unwrap();
    evaluator.register_function("*", Function::new(2, Box::new(functions::multiplication))).unwrap();
    evaluator.register_function("/", Function::new(2, Box::new(functions::division))).unwrap();
    evaluator.register_function("^", Function::new(2, Box::new(functions::exponentiation))).unwrap();

    evaluator.register_function("log", Function::new(2, Box::new(functions::log))).unwrap();
    evaluator.register_function("log10", Function::new(1, Box::new(functions::log10))).unwrap();
    evaluator.register_function("bind", Function::new(2, Box::new(functions::bind))).unwrap();

    PolynomialEvaluator {
      evaluator: evaluator
    }
  }
}

/// Allows usage of PolynomialEvaluator as common TokensReducer
impl TokensReducer for PolynomialEvaluator {
  fn process(&self, tokens: &Tokens) -> Result<Polynomial, EvaluationError> {
    self.evaluator.process(tokens)
  }
}

/// Extends Parser with common arithmetic operators with correct precedence
/// and associativity.
pub struct PolynomialParser {
  /// Underlying parser (one can use it to extend it furthermore)
  pub parser: Parser
}

/// Creates PolynomialParser and extends basic Parser.
///
/// Common arithmetic operators are registered with the Parser.
impl Default for PolynomialParser {
  fn default() -> PolynomialParser {
    let mut parser = Parser::default();

    parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator::new(5, OperatorAssociativity::Left));
    parser.register_operator('/', Operator::new(5, OperatorAssociativity::Left));
    parser.register_operator('^', Operator::new(10, OperatorAssociativity::Right));

    PolynomialParser {
      parser: parser
    }
  }
}

/// Allows usage of PolynomialParser as common TokensProcessor
impl TokensProcessor for PolynomialParser {
  fn process(&mut self, tokens: &Tokens) -> Result<&Tokens, ParsingError> {
    self.parser.process(tokens)
  }
}

/// Implementations of function handlers used in operators and functions.
///
/// This module is public, so when you are writing another evaluator, but
/// it does not extend PolynomialEvaluator, you can reuse these functions
/// as handlers for some of the common operations.
///
/// Operations that are directly defined on the Polynomial (such as addition,
/// subtraction, multiplication and division), avoid cloning by using
/// the assignment with operation, thus optimizing memory usage.
pub mod functions {
  use polynomial::Polynomial;
  use EvaluationError;

  /// Adds two polynomials together (requires two arguments).
  pub fn addition(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a += b;
    Ok(a)
  }

  /// Subtracts two polynomials from each other (requires two arguments).
  pub fn subtraction(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a -= b;
    Ok(a)
  }

  /// Multiplies two polynomials together (requires two arguments).
  pub fn multiplication(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a *= b;
    Ok(a)
  }

  /// Divides two polynomials by each other (requires two arguments).
  ///
  /// # Errors
  ///
  /// It will return a wrapped PolynomialError when a degree of divident is
  /// smaller than a degree of divisor or when a divident is non-constant
  /// polynomial, while a divisor is a zero.
  pub fn division(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    match (&mut a) / &b {
      Ok(_) => Ok(a),
      Err(e) => Err(EvaluationError::PolynomialError(e))
    }
  }

  /// Computes a logarithm of arbitrary base (requires two constant arguments).
  ///
  /// First arguments is a value to have a logarithm computed on, where a second
  /// argument is a base of the logarithm.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial_calculator::PolynomialCalculator;
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::calculator::Calculator;
  /// assert_eq!(PolynomialCalculator.process("log(100, 10)"), Ok(Polynomial::constant(2.0)));
  /// assert_eq!(PolynomialCalculator.process("log(256, 2)"), Ok(Polynomial::constant(8.0)));
  /// ```
  ///
  /// # Errors
  ///
  /// It will return a wrapped PolynomialError::NonConstantError when any of the
  /// arguments is not a constant polynomial (a polynomial of degree zero).
  pub fn log(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].as_f64()).log(try!(args[1].as_f64()))))
  }

  /// Computes a decimal logarithm (requires a single constant argument).
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial_calculator::PolynomialCalculator;
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::calculator::Calculator;
  /// assert_eq!(PolynomialCalculator.process("log10(100)"), Ok(Polynomial::constant(2.0)));
  /// ```
  ///
  /// # Errors
  ///
  /// It will return a wrapped PolynomialError::NonConstantError when the argument
  /// is not a constant polynomial (a polynomial of degree zero).
  pub fn log10(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].as_f64()).log10()))
  }

  /// Binds a polynomial with a value (requires two arguments).
  ///
  /// This function computes value of given polynomial (first argument) when
  /// the symbol is replaced with a constant value (second argument).
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial_calculator::PolynomialCalculator;
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::calculator::Calculator;
  /// assert_eq!(PolynomialCalculator.process("bind(x^2, 10)"), Ok(Polynomial::constant(100.0)));
  /// ```
  ///
  /// # Errors
  ///
  /// It will return a wrapped PolynomialError::NonConstantError when the second
  /// argument is not a constant polynomial (a polynomial of degree zero).
  pub fn bind(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].bind(try!(args[1].as_f64())))
  }

  /// Performs exponentiation of polynomial (requires two arguments).
  ///
  /// First argument is an exponentiation base, where second argument is
  /// the exponent (which must be a constant polynomial). Method of exponentiation
  /// is optimized, it depends on degree of the base and a value of the exponent.
  /// Exponentation of complicated polynomials is done subefficiently by multiplication.
  ///
  /// # Errors
  ///
  /// It will return a NonConstantExponent error when the exponient is not
  /// a constant polynomial. Performing such operation would result in a
  /// non-polynomial result.
  ///
  /// It will return a NonNaturalExponent error when the exponient is not
  /// a natural number and the base is not a constant polynomial. Performing
  /// such operation would result in a non-polynomial result.
  pub fn exponentiation(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let exponent = args.pop().unwrap();
    let base = args.pop().unwrap();

    let base_degree = base.degree();
    let exponent_degree = exponent.degree();

    if exponent_degree > 0 {
      Err(EvaluationError::NonConstantExponent)
    } else
    if exponent[0] == 0.0 {
      Ok(Polynomial::constant(1.0))
    } else
    if base_degree == 0 {
      Ok(Polynomial::constant(base[0].powf(exponent[0])))
    } else
    if exponent[0] > 0.0 && exponent[0].fract() == 0.0 {
      if base_degree == 1 && base[0] == 0.0 {
        let mut v = Polynomial::zero();
        v[exponent[0] as usize] = base[1].powf(exponent[0]);

        Ok(v)
      } else {
        let mut v = base.clone();
        let exp = exponent[0] as usize;

        {
          let mut vr = &mut v;
          for _ in 1..exp {
            vr *= &base;
          }
        }

        Ok(v)
      }
    } else {
      Err(EvaluationError::NonNaturalExponent)
    }
  }
}

#[cfg(test)]
mod tests {
  use polynomial::{Polynomial, PolynomialError};
  use polynomial_calculator::PolynomialCalculator;
  use EvaluationError;
  use calculator::Calculator;
  use calculator::CalculationError;
  use std::f64::consts::{PI, E};

  #[test]
  fn test_general() {
    assert_eq!(PolynomialCalculator.process("(3+(4-1))*5"), Ok(Polynomial::constant(30.0)));
  }

  #[test]
  fn test_constants() {
    assert_eq!(PolynomialCalculator.process("x"), Ok(Polynomial::linear(0.0, 1.0)));
    assert_eq!(PolynomialCalculator.process("pi"), Ok(Polynomial::constant(PI)));
    assert_eq!(PolynomialCalculator.process("e"), Ok(Polynomial::constant(E)));
  }

  #[test]
  fn test_functions() {
    assert_eq!(PolynomialCalculator.process("log(256, 2)"), Ok(Polynomial::constant(8.0)));
    assert_eq!(PolynomialCalculator.process("log10(100)"), Ok(Polynomial::constant(2.0)));
    assert_eq!(PolynomialCalculator.process("bind(x^2, 10)"), Ok(Polynomial::constant(100.0)));
  }

  #[test]
  fn test_operations() {
    assert_eq!(PolynomialCalculator.process("1+1"), Ok(Polynomial::constant(2.0)));
    assert_eq!(PolynomialCalculator.process("1+-1"), Ok(Polynomial::constant(0.0)));

    assert_eq!(PolynomialCalculator.process("1-1"), Ok(Polynomial::constant(0.0)));
    assert_eq!(PolynomialCalculator.process("1-3"), Ok(Polynomial::constant(-2.0)));
    assert_eq!(PolynomialCalculator.process("1--1"), Ok(Polynomial::constant(2.0)));

    assert_eq!(PolynomialCalculator.process("2*4"), Ok(Polynomial::constant(8.0)));
    assert_eq!(PolynomialCalculator.process("2*0"), Ok(Polynomial::constant(0.0)));

    assert_eq!(PolynomialCalculator.process("2/4"), Ok(Polynomial::constant(0.5)));
    assert!(PolynomialCalculator.process("2/0").unwrap().as_f64().unwrap().is_infinite());
    assert!(PolynomialCalculator.process("0/0").unwrap().as_f64().unwrap().is_nan());

    assert_eq!(PolynomialCalculator.process("2^0"), Ok(Polynomial::constant(1.0)));
    assert_eq!(PolynomialCalculator.process("2^4"), Ok(Polynomial::constant(16.0)));
  }

  #[test]
  fn test_polynomials() {
    assert_eq!(PolynomialCalculator.process("2x+1"), Ok(Polynomial::new(&[1.0, 2.0])));
    assert_eq!(PolynomialCalculator.process("2x+4x"), Ok(Polynomial::new(&[0.0, 6.0])));
    assert_eq!(PolynomialCalculator.process("2x-2x-1"), Ok(Polynomial::new(&[-1.0])));
    assert_eq!(PolynomialCalculator.process("2x--2x"), Ok(Polynomial::new(&[0.0, 4.0])));
    assert_eq!(PolynomialCalculator.process("2x*4x"), Ok(Polynomial::new(&[0.0, 0.0, 8.0])));
    assert_eq!(PolynomialCalculator.process("2x*(4x+1)"), Ok(Polynomial::new(&[0.0, 2.0, 8.0])));
    assert_eq!(PolynomialCalculator.process("2x/x"), Ok(Polynomial::new(&[2.0])));
    assert_eq!(PolynomialCalculator.process("2x/0"), Err(CalculationError::EvaluationError(EvaluationError::PolynomialError(PolynomialError::DivisionByZero))));
    assert_eq!(PolynomialCalculator.process("2x/x^2"), Err(CalculationError::EvaluationError(EvaluationError::PolynomialError(PolynomialError::DividentDegreeMismatch))));
    assert_eq!(PolynomialCalculator.process("(x^2-3x-10)/(x+2)"), Ok(Polynomial::new(&[-5.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("x^5"), Ok(Polynomial::new(&[0.0, 0.0, 0.0, 0.0, 0.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("(x+1)^5"), Ok(Polynomial::new(&[1.0, 5.0, 10.0, 10.0, 5.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("2^x"), Err(CalculationError::EvaluationError(EvaluationError::NonConstantExponent)));
    assert_eq!(PolynomialCalculator.process("x^3.14"), Err(CalculationError::EvaluationError(EvaluationError::NonNaturalExponent)));
  }
}
