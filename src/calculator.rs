//! `Calculator` is an easy to use generic method of evaluating string expressions.

use super::*;
use polynomial::Polynomial;

/// `CalculationError` wraps parsing and evaluation errors
#[derive(Debug, PartialEq)]
pub enum CalculationError {
  /// `ParsingError` returned from `TokensProcessor`
  ParsingError(ParsingError),
  /// `EvaluationError` returned from `TokensReducer`
  EvaluationError(EvaluationError)
}

/// Wraps `ParsingError` in `CalculationError`
impl From<ParsingError> for CalculationError {
  fn from(e: ParsingError) -> CalculationError {
    CalculationError::ParsingError(e)
  }
}

/// Wraps `EvaluationError` in `CalculationError`
impl From<EvaluationError> for CalculationError {
  fn from(e: EvaluationError) -> CalculationError {
    CalculationError::EvaluationError(e)
  }
}

/// Calculator is the easiest way of evaluating string expressions
/// into a `Polynomial` value.
///
/// A struct which is a calculator (implements this trait) can easily
/// perform evaluation using given `StringProcessor`, `TokensProcessor`
/// and `TokensReducer`.
pub trait Calculator<T, P, E>
  where T: StringProcessor + Default,
        P: TokensProcessor + Default,
        E: TokensReducer + Default {

  /// Takes string and evaluates it into a Polynomial.
  ///
  /// This method creates a new instance of tokenizer, parser
  /// and evaluator for each execution. While it is easy to
  /// use, it is not the quickest way of evaluation when there
  /// are multiple expression.
  fn process(&self, line: &str) -> Result<Polynomial, CalculationError> {
    let mut tokenizer = T::default();
    let mut parser = P::default();
    let evaluator = E::default();

    let tokens = tokenizer.process(line);
    let parsed_tokens = try!(parser.process(tokens));
    let evaluated = try!(evaluator.process(parsed_tokens));

    Ok(evaluated)
  }
}
