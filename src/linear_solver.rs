//! Defines a LinearSolver which extends a PolynomialCalculator with
//! ability of solving single linear equation.
//!
//! It supports the very same operations and functions as the
//! PolynomialCalculator, however a new operator `=` is defined which
//! solves a linear equation.
//!
//! One can use LinearSolverParser, LinearSolverEvaluator or functions
//! module in their own implementations, so there is no need of reimplementing
//! this functionality.
//!
//! # Examples
//!
//! A LinearSolver provides an easy way to integrate a solver and calculator into
//! your project. It simply takes a string expression and returns evaluated value,
//! however if you need high-efficiency solution you should consider using
//! LinearSolverParser and LinearSolverEvaluator directly.
//!
//! ```
//! use xxcalc::linear_solver::LinearSolver;
//! use xxcalc::calculator::Calculator;
//! use xxcalc::polynomial::Polynomial;
//!
//! assert_eq!(LinearSolver.process("2 * x + 0.5 = 1"), Ok(Polynomial::constant(0.25)));
//! assert_eq!(LinearSolver.process("2x + 1 = 2(1-x)"), Ok(Polynomial::constant(0.25)));
//! assert_eq!(LinearSolver.process("x^2-x^2+x=2"), Ok(Polynomial::constant(2.0)));
//! assert_eq!(LinearSolver.process("1-x=x"), Ok(Polynomial::constant(0.5)));
//! ```

use super::*;
use calculator::Calculator;
use evaluator::{Evaluator, Function};
use parser::{Parser, Operator, OperatorAssociativity};
use tokenizer::Tokenizer;
use polynomial_calculator::{PolynomialParser, PolynomialEvaluator};
use polynomial::Polynomial;

/// LinearSolver is a calculator using a LinearSolverParser and a LinearSolverEvaluator,
/// to provide multiple arithmetic operations and basic linear solver capability.
///
/// The solver support the same operators as a PolynomialCalculator, but it adds
/// `=` operator which tries to solve value of `x` and returns it.
///
/// While usage of the solver is the easiest way of embedding solving engine into
/// your program, please note that a Tokenizer, LinearSolverParser and LinearSolverEvaluator
/// is created with each call, which requires reallocation of memory.
///
/// # Examples
/// ```
/// # use xxcalc::linear_solver::LinearSolver;
/// # use xxcalc::calculator::Calculator;
/// # use xxcalc::polynomial::Polynomial;
/// assert_eq!(LinearSolver.process("2 * x + 0.5 = 1"), Ok(Polynomial::constant(0.25)));
/// assert_eq!(LinearSolver.process("2x + 1 = 2(1-x)"), Ok(Polynomial::constant(0.25)));
/// assert_eq!(LinearSolver.process("x^2-x^2+x=2"), Ok(Polynomial::constant(2.0)));
/// assert_eq!(LinearSolver.process("1-x=x"), Ok(Polynomial::constant(0.5)));
/// ```
pub struct LinearSolver;

impl Calculator<Tokenizer, LinearSolverParser, LinearSolverEvaluator> for LinearSolver {

}

/// Extends PolynomialEvaluator with handler for linear solver operator.
pub struct LinearSolverEvaluator {
  /// Underlying evaluator (one can use it to extend it furthermore)
  pub evaluator: Evaluator
}

/// Creates a LinearSolverEvaluator and extends the PolynomialEvaluator.
///
/// Handler for linear solver operator is registered to the underlying evalutor.
impl Default for LinearSolverEvaluator {
  fn default() -> LinearSolverEvaluator {
    let mut evaluator = PolynomialEvaluator::default().evaluator;

    evaluator.register_function("=", Function::new(2, Box::new(functions::solver))).unwrap();

    LinearSolverEvaluator {
      evaluator: evaluator
    }
  }
}

/// Allows usage of LinearSolverEvaluator as common TokensReducer
impl TokensReducer for LinearSolverEvaluator {
  fn process(&self, tokens: &Tokens) -> Result<Polynomial, EvaluationError> {
    self.evaluator.process(tokens)
  }
}

/// Extends PolynomialParser with a solving operator `=` with minimal
/// precedence.
pub struct LinearSolverParser {
  /// Underlying parser (one can use it to extend it furthermore)
  pub parser: Parser
}

use std::i64;

/// Creates LinearSolverParser and extends a PolynomialParser.
///
/// A linear solving operator `=` is registered to the PolynomialParser. Its
/// precedence is minimal, so LHS and RHS are always evaluated before solving.
impl Default for LinearSolverParser {
  fn default() -> LinearSolverParser {
    let mut parser = PolynomialParser::default().parser;

    parser.register_operator('=', Operator::new(i64::MIN, OperatorAssociativity::Left));

    LinearSolverParser {
      parser: parser
    }
  }
}

/// Allows usage of LinearSolverParser as common TokensProcessor
impl TokensProcessor for LinearSolverParser {
  fn process(&mut self, tokens: &Tokens) -> Result<&Tokens, ParsingError> {
    self.parser.process(tokens)
  }
}

/// Implementation of solving operator handler.
///
/// This module is public, so when you are writing another evaluator, but
/// it does not extend LinearSolverEvaluator, you can reuse this handler
/// without reimplementing.
pub mod functions {
  use super::*;
  use polynomial::Polynomial;
  use EvaluationError;

  /// Solves a linear equation for a value of `x` (requires two arguments).
  ///
  /// Solving is done by moving `x` coefficients to LHS and constants to RHS,
  /// than after a scaling (division by x coefficient), a value of `x` is
  /// obtained.
  ///
  /// # Errors
  ///
  /// The solver detects multiple situations where solving is not possible.
  ///
  /// A NonLinear error is returned when provided equation is not linear (has
  /// a polynomial of degree greater than one).
  ///
  /// ```
  /// # use xxcalc::linear_solver::{LinearSolver, SolvingError};
  /// # use xxcalc::calculator::{Calculator, CalculationError};
  /// # use xxcalc::EvaluationError;
  /// assert_eq!(LinearSolver.process("x^2=1").unwrap_err(), CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::NonLinear)));
  /// ```
  ///
  /// A NoSymbol error is returned when provided expression is not really an equation
  /// to solve, as there is no symbol `x` used.
  ///
  /// ```
  /// # use xxcalc::linear_solver::{LinearSolver, SolvingError};
  /// # use xxcalc::calculator::{Calculator, CalculationError};
  /// # use xxcalc::EvaluationError;
  /// assert_eq!(LinearSolver.process("0=0").unwrap_err(), CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::NoSymbol)));
  /// ```
  ///
  /// A Tautology error is returned when provided equation is solvable for any
  /// value of `x`.
  ///
  /// ```
  /// # use xxcalc::linear_solver::{LinearSolver, SolvingError};
  /// # use xxcalc::calculator::{Calculator, CalculationError};
  /// # use xxcalc::EvaluationError;
  /// assert_eq!(LinearSolver.process("x=x").unwrap_err(), CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::Tautology)));
  /// ```
  ///
  /// A NonSolvable error is returned when provided equation has no solutions.
  ///
  /// ```
  /// # use xxcalc::linear_solver::{LinearSolver, SolvingError};
  /// # use xxcalc::calculator::{Calculator, CalculationError};
  /// # use xxcalc::EvaluationError;
  /// assert_eq!(LinearSolver.process("x=x+1").unwrap_err(), CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::NonSolvable)));
  /// ```
  pub fn solver(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let mut right = args.pop().unwrap();
    let mut left = args.pop().unwrap();

    let right_degree = right.degree();
    let left_degree = left.degree();

    if left_degree > 1 || right_degree > 1 {
      Err(EvaluationError::SolvingError(SolvingError::NonLinear))
    } else
    if left_degree == 0 && right_degree == 0 {
      Err(EvaluationError::SolvingError(SolvingError::NoSymbol))
    } else {
      if right_degree > 0 {
        left[1] -= right[1];
        right[1] -= right[1];
      }

      right[0] -= left[0];
      left[0] -= left[0];

      right[0] /= left[1];
      left[1] /= left[1];

      if right[0].is_nan() {
        Err(EvaluationError::SolvingError(SolvingError::Tautology))
      } else
      if right[0].is_infinite() {
        Err(EvaluationError::SolvingError(SolvingError::NonSolvable))
      } else {
        Ok(right)
      }
    }
  }
}

/// An error that occurs during linear solving.
#[derive(Debug, PartialEq)]
pub enum SolvingError {
  /// Provided expression is non linear (contains polynomials of degree
  /// greater than one).
  NonLinear,

  /// Expression contains only constants (no `x` symbol), so there is
  /// nothing to solve.
  NoSymbol,

  /// The equation is solvable for any value of `x` (it is always true).
  Tautology,

  /// The equation cannot be solved at all (as there is no such value of
  /// `x` which would make the equation true).
  NonSolvable
}

#[cfg(test)]
mod tests {
  use super::*;
  use EvaluationError;
  use polynomial::Polynomial;
  use calculator::{Calculator, CalculationError};

  #[test]
  fn test_general() {
    assert_eq!(LinearSolver.process("2 * x + 0.5 = 1"), Ok(Polynomial::constant(0.25)));
    assert_eq!(LinearSolver.process("2x + 1 = 2(1-x)"), Ok(Polynomial::constant(0.25)));
    assert_eq!(LinearSolver.process("x^2-x^2+x=2"), Ok(Polynomial::constant(2.0)));
    assert_eq!(LinearSolver.process("1-x=x"), Ok(Polynomial::constant(0.5)));
  }

  #[test]
  fn test_position_agnostic() {
    assert_eq!(LinearSolver.process("x=2"), Ok(Polynomial::constant(2.0)));
    assert_eq!(LinearSolver.process("2=x"), Ok(Polynomial::constant(2.0)));
    assert_eq!(LinearSolver.process("x-2=0"), Ok(Polynomial::constant(2.0)));
    assert_eq!(LinearSolver.process("0=-2+x"), Ok(Polynomial::constant(2.0)));
  }

  #[test]
  fn test_restrictions() {
    assert_eq!(LinearSolver.process("x^2=5"), Err(CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::NonLinear))));
    assert_eq!(LinearSolver.process("2=2"), Err(CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::NoSymbol))));
  }

  #[test]
  fn test_special_cases() {
    assert_eq!(LinearSolver.process("x=x"), Err(CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::Tautology))));
    assert_eq!(LinearSolver.process("x=x+1"), Err(CalculationError::EvaluationError(EvaluationError::SolvingError(SolvingError::NonSolvable))));
  }
}
