use tokenizer::StringProcessor;
use parser::{TokensProcessor, ParsingError};
use evaluator::{TokensReducer, EvaluationError};
use polynomial::Polynomial;

#[derive(Debug, PartialEq)]
pub enum CalculationError {
  ParsingError(ParsingError),
  EvaluationError(EvaluationError)
}

impl From<ParsingError> for CalculationError {
  fn from(e: ParsingError) -> CalculationError {
    CalculationError::ParsingError(e)
  }
}

impl From<EvaluationError> for CalculationError {
  fn from(e: EvaluationError) -> CalculationError {
    CalculationError::EvaluationError(e)
  }
}

pub trait Calculator<T, P, E>
  where T: StringProcessor + Default,
        P: TokensProcessor + Default,
        E: TokensReducer + Default {
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
