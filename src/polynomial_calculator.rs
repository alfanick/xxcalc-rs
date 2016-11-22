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

  pub fn addition(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a += b;
    Ok(a)
  }

  pub fn subtraction(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a -= b;
    Ok(a)
  }

  pub fn multiplication(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a *= b;
    Ok(a)
  }

  pub fn division(mut args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    let b = args.pop().unwrap();
    let mut a = args.pop().unwrap();

    a /= b;
    Ok(a)
  }

  pub fn log(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].as_f64()).log(try!(args[1].as_f64()))))
  }

  pub fn log10(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(Polynomial::constant(try!(args[0].as_f64()).log10()))
  }

  pub fn bind(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].bind(try!(args[1].as_f64())))
  }

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
    assert_eq!(PolynomialCalculator.process("(x^2-3x-10)/(x+2)"), Ok(Polynomial::new(&[-5.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("x^5"), Ok(Polynomial::new(&[0.0, 0.0, 0.0, 0.0, 0.0, 1.0])));
    assert_eq!(PolynomialCalculator.process("(x+1)^5"), Ok(Polynomial::new(&[1.0, 5.0, 10.0, 10.0, 5.0, 1.0])));
  }
}