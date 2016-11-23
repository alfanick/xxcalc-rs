use polynomial::{Polynomial, PolynomialError};
use tokenizer::{Token, Tokens};
use std::collections::BTreeMap;
use linear_solver::SolvingError;


#[derive(Debug, PartialEq)]
pub enum EvaluationError {
  UnknownSymbol(String, usize),
  ArgumentMissing(String, usize, usize),
  MultipleExpressions,
  ConflictingName(String),
  PolynomialError(PolynomialError),
  SolvingError(SolvingError),
  NonConstantExponent,
  NonNaturalExponent
}

pub trait TokensReducer {
  fn process(&self, tokens: &Tokens) -> Result<Polynomial, EvaluationError>;
}

pub type FunctionHandle = Box<Fn(Vec<Polynomial>) -> Result<Polynomial, EvaluationError>>;

pub struct Function {
  arity: usize,
  handle: FunctionHandle
}

impl Function {
  pub fn new(a: usize, h: FunctionHandle) -> Function {
    Function {
      arity: a,
      handle: h
    }
  }
}

pub struct Evaluator {
  functions: BTreeMap<String, Function>,
  constants: BTreeMap<String, Polynomial>
}

impl From<PolynomialError> for EvaluationError {
  fn from(e: PolynomialError) -> EvaluationError {
    EvaluationError::PolynomialError(e)
  }
}

impl Default for Evaluator {
  fn default() -> Evaluator {
    Evaluator::new()
  }
}

impl TokensReducer for Evaluator {
  fn process(&self, tokens_with_identifiers: &Tokens) -> Result<Polynomial, EvaluationError> {
    let mut stack: Vec<Polynomial> = Vec::with_capacity(10);
    let &Tokens(ref tokens, ref identifiers) = tokens_with_identifiers;

    for &(position, ref token) in tokens {
      match *token {
        Token::Number(x) => stack.push(Polynomial::constant(x)),
        Token::Operator(x) => {
          let result = try!(self.call_function(&x.to_string(), position, &mut stack));
          stack.push(result);
        },
        Token::Identifier(idx) => {
          let x = identifiers.get(idx).unwrap();

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
  pub fn new() -> Evaluator {
    Evaluator {
      functions: BTreeMap::new(),
      constants: BTreeMap::new()
    }
  }

  #[inline(always)]
  fn call_function(&self, name: &String, position: usize, stack: &mut Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    if let Some(function) = self.functions.get(name) {
      if stack.len() < function.arity {
        Err(EvaluationError::ArgumentMissing(name.clone(), function.arity, position))
      } else {
        let stack_len = stack.len();
        let args: Vec<Polynomial> = stack.split_off(stack_len - function.arity);

        (function.handle)(args)
      }
    } else {
      Err(EvaluationError::UnknownSymbol(name.clone(), position))
    }
  }

  pub fn register_function(&mut self, name: &str, function: Function) -> Result<Option<Function>, EvaluationError> {
    if let Some(_) = self.constants.get(name) {
      return Err(EvaluationError::ConflictingName(name.to_string()));
    }

    Ok(self.functions.insert(name.to_string(), function))
  }

  pub fn register_constant(&mut self, name: &str, constant: Polynomial) -> Result<Option<Polynomial>, EvaluationError> {
    if let Some(_) = self.functions.get(name) {
      return Err(EvaluationError::ConflictingName(name.to_string()));
    }

    Ok(self.constants.insert(name.to_string(), constant))
  }
}

#[cfg(test)]
#[allow(unused_must_use)]
mod tests {
  use evaluator::*;
  use parser::*;
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

#[cfg(test)]
mod benchmarks {
  use super::*;
  use parser::*;
  use tokenizer::*;
  use tokenizer::benchmarks::add_sub_gen;
  use test::Bencher;
  use polynomial_calculator::functions::{addition, subtraction};
  use polynomial::Polynomial;

  #[bench]
  #[ignore]
  fn bench_evaluation_cloning(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process(add_sub_r);
    let mut parser = Parser::new();
    let _ = parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    let _ = parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));
    let parsed_tokens = parser.process(tokens).unwrap();
    let mut evaluator = Evaluator::new();

    let _ = evaluator.register_function("+", Function::new(2, Box::new(|args| {
      Ok(args[0].clone() + args[1].clone())
    })));
    let _ = evaluator.register_function("-", Function::new(2, Box::new(|args| {
      Ok(args[0].clone() + args[1].clone())
    })));

    b.iter(|| {
      (0..10).fold(0.0, |a, _| a + evaluator.process(parsed_tokens).unwrap()[0])
    });
  }

  #[bench]
  #[ignore]
  fn bench_evaluation(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process(add_sub_r);
    let mut parser = Parser::new();
    let _ = parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    let _ = parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));
    let parsed_tokens = parser.process(tokens).unwrap();
    let mut evaluator = Evaluator::new();

    let _ = evaluator.register_function("+", Function::new(2, Box::new(addition)));
    let _ = evaluator.register_function("-", Function::new(2, Box::new(subtraction)));

    b.iter(|| {
      (0..10).fold(0.0, |a, _| a + evaluator.process(parsed_tokens).unwrap()[0])
    });
  }

  #[bench]
  fn bench_evaluation_numbers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process("3.14");
    let mut parser = Parser::new();
    let parsed_tokens = parser.process(tokens).unwrap();
    let evaluator = Evaluator::new();

    b.iter(|| {
      evaluator.process(parsed_tokens).unwrap()
    });
  }

  #[bench]
  fn bench_evaluation_constants(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process("pi");
    let mut parser = Parser::new();
    let parsed_tokens = parser.process(tokens).unwrap();
    let mut evaluator = Evaluator::new();
    let _ = evaluator.register_constant("pi", Polynomial::constant(3.14));

    b.iter(|| {
      evaluator.process(parsed_tokens).unwrap()
    });
  }

}
