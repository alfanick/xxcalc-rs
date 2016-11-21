use calculator::*;
use tokenizer::{TokenList, Tokenizer};
use evaluator::{Evaluator, EvaluationError, TokensReducer, Function};
use parser::{Parser, ParsingError, Operator, OperatorAssociativity, TokensProcessor};
use polynomial::Polynomial;
use std::f64::consts::{PI, E};

pub struct PolynomialCalculator;

impl PolynomialCalculator {

}

impl Calculator<Tokenizer, PolynomialParser, PolynomialEvaluator> for PolynomialCalculator {

}

pub struct PolynomialEvaluator {
  pub evaluator: Evaluator
}

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

impl TokensReducer for PolynomialEvaluator {
  fn process(&self, tokens: TokenList) -> Result<Polynomial, EvaluationError> {
    self.evaluator.process(tokens)
  }
}

pub struct PolynomialParser {
  pub parser: Parser
}

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

impl TokensProcessor for PolynomialParser {
  fn process(&self, tokens: TokenList) -> Result<TokenList, ParsingError> {
    self.parser.process(tokens)
  }
}

mod functions {
  use polynomial::Polynomial;
  use evaluator::EvaluationError;

  pub fn addition(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() + args[1].clone())
  }

  pub fn subtraction(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() - args[1].clone())
  }

  pub fn multiplication(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() * args[1].clone())
  }

  pub fn division(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() / args[1].clone())
  }

  pub fn log(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].clone().as_f64()).log(try!(args[1].clone().as_f64()))))
  }

  pub fn log10(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].clone().as_f64()).log10()))
  }

  pub fn bind(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone().bind(try!(args[1].clone().as_f64())))
  }

  pub fn exponentiation(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    let base = args[0].clone();
    let exponent = args[1].clone();

    let base_degree = base.degree();
    let exponent_degree = exponent.degree();

    if exponent_degree > 0 {
      Err(EvaluationError::NonConstantExponent)
    } else
    if base_degree == 0 {
      Ok(Polynomial::constant(try!(base.as_f64()).powf(try!(exponent.as_f64()))))
    } else
    if try!(exponent.as_f64()).fract() == 0.0 {
      if base_degree == 1 && base[0] == 0.0 {
        let mut v = Polynomial::zero();
        v[exponent[0] as usize] = base[1].powf(exponent[0]);

        Ok(v)
      } else {
        let mut v = base.clone();
        let exp = try!(exponent.as_f64()) as usize;

        for _ in 1..exp {
          v *= base.clone();
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
  use polynomial::Polynomial;
  use polynomial_calculator::PolynomialCalculator;
  use calculator::Calculator;
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
    assert_eq!(PolynomialCalculator.process("(x^2-3x-10)/(x+2)"), Ok(Polynomial::new(&[-5.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("x^5"), Ok(Polynomial::new(&[0.0, 0.0, 0.0, 0.0, 0.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("(x+1)^5"), Ok(Polynomial::new(&[1.0, 5.0, 10.0, 10.0, 5.0, 1.0])));
  }
}