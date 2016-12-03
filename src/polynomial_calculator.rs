//! Defines a PolynomialCalculator with common arithmetic operations, functions
//! and constants already defined.

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
///
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
  /// # Errors
  ///
  /// It will return a wrapped PolynomialError::NonConstantError when any of the
  /// arguments is not a constant polynomial (a polynomial of degree zero).
  pub fn log(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].as_f64()).log(try!(args[1].as_f64()))))
  }

  /// Computes a decimal logarithm (requires a single constant argument).
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
  /// # Errors
  ///
  /// It will return a wrapper PolynomialError::NonConstantError when the second
  /// argument is not a constant polynomial (a polynomial of degree zero).
  pub fn bind(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].bind(try!(args[1].as_f64())))
  }

  /// Performs exponentiation of polynomial (requires two arguments).
  ///
  /// First argument is an exponentiation base, where second argument is
  /// the exponent (which must be a constant polynomial).
  pub fn exponentiation(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let exponent = args.pop().unwrap();
    let base = args.pop().unwrap();

    let base_degree = base.degree();
    let exponent_degree = exponent.degree();

    if exponent_degree > 0 {
      Err(EvaluationError::NonConstantExponent)
    } else
    if base_degree == 0 {
      Ok(Polynomial::constant(base[0].powf(exponent[0])))
    } else
    if exponent[0] >= 0.0 && exponent[0].fract() == 0.0 {
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
  }
}
