use calculator::*;
use evaluator::*;
use parser::*;
use tokenizer::{TokenList, Tokenizer};
use polynomial_calculator::*;
use polynomial::Polynomial;

#[derive(Debug, PartialEq)]
pub enum SolvingError {
  NonLinear,
  NoSymbol,
  Tautology,
  NonSolvable
}

pub struct LinearSolver;

impl Calculator<Tokenizer, LinearSolverParser, LinearSolverEvaluator> for LinearSolver {

}

pub struct LinearSolverEvaluator {
  pub evaluator: Evaluator
}

impl Default for LinearSolverEvaluator {
  fn default() -> LinearSolverEvaluator {
    let mut evaluator = PolynomialEvaluator::default().evaluator;

    evaluator.register_function("=", Function::new(2, Box::new(functions::solver))).unwrap();

    LinearSolverEvaluator {
      evaluator: evaluator
    }
  }
}

impl TokensReducer for LinearSolverEvaluator {
  fn process(&self, tokens: TokenList) -> Result<Polynomial, EvaluationError> {
    self.evaluator.process(tokens)
  }
}

pub struct LinearSolverParser {
  pub parser: Parser
}

use std::i64;

impl Default for LinearSolverParser {
  fn default() -> LinearSolverParser {
    let mut parser = PolynomialParser::default().parser;

    parser.register_operator('=', Operator::new(i64::MIN, OperatorAssociativity::Left));

    LinearSolverParser {
      parser: parser
    }
  }
}

impl TokensProcessor for LinearSolverParser {
  fn process(&self, tokens: TokenList) -> Result<TokenList, ParsingError> {
    self.parser.process(tokens)
  }
}

mod functions {
  use super::*;
  use evaluator::EvaluationError;
  use polynomial::Polynomial;

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

#[cfg(test)]
mod tests {
  use super::*;
  use polynomial::Polynomial;
  use calculator::{Calculator, CalculationError};
  use evaluator::EvaluationError;

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