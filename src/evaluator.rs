use polynomial::{Polynomial, PolynomialError};
use tokenizer::{TokenList, Token};
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
  fn process(&self, tokens: TokenList) -> Result<Polynomial, EvaluationError>;
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
  fn process(&self, tokens: TokenList) -> Result<Polynomial, EvaluationError> {
    let mut stack: Vec<Polynomial> = Vec::with_capacity(10);

    for (position, token) in tokens {
      match token {
        Token::Number(x) => stack.push(Polynomial::constant(x)),
        Token::Operator(x) => {
          let result = try!(self.call_function(&x.to_string(), position, &mut stack));
          stack.push(result);
        },
        Token::Identifier(x) => {
          if let Some(constant) = self.constants.get(&x) {
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

  fn addition(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() + args[1].clone())
  }

  fn subtraction(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() - args[1].clone())
  }

  fn multiplication(args: Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
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

    assert_eq!(evaluator.process(parser.process(tokenize("2+4")).unwrap()), Ok(Polynomial::constant(6.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("2*4")).unwrap()), Ok(Polynomial::constant(8.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("2+4*6")).unwrap()), Ok(Polynomial::constant(26.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("2*4+6")).unwrap()), Ok(Polynomial::constant(14.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("(2+4)*6")).unwrap()), Ok(Polynomial::constant(36.0)));

    assert_eq!(evaluator.process(parser.process(tokenize("2+-4")).unwrap()), Ok(Polynomial::constant(-2.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("2--4")).unwrap()), Ok(Polynomial::constant(6.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("2++4")).unwrap()), Ok(Polynomial::constant(6.0)));
  }

  #[test]
  fn test_constants() {
    let mut evaluator = Evaluator::new();
    let parser = Parser::new();

    assert_eq!(evaluator.process(parser.process(tokenize("foo")).unwrap()), Err(EvaluationError::UnknownSymbol("foo".to_string(), 0)));

    evaluator.register_constant("foo", Polynomial::constant(123.0));
    assert_eq!(evaluator.process(parser.process(tokenize("foo")).unwrap()), Ok(Polynomial::constant(123.0)));
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

    assert_eq!(evaluator.process(parser.process(tokenize("double(2)")).unwrap()), Err(EvaluationError::UnknownSymbol("double".to_string(), 0)));

    evaluator.register_function("double", Function::new(1, Box::new(|args|{
      Ok(args[0].clone() * Polynomial::constant(2.0))
    })));

    assert_eq!(evaluator.process(parser.process(tokenize("double(2)")).unwrap()), Ok(Polynomial::constant(4.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("double(4*-0.5)")).unwrap()), Ok(Polynomial::constant(-4.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("double()")).unwrap()), Err(EvaluationError::ArgumentMissing("double".to_string(), 1, 0)));
    assert_eq!(evaluator.process(parser.process(tokenize("double(1, 2)")).unwrap()), Err(EvaluationError::MultipleExpressions));
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

    assert_eq!(evaluator.process(parser.process(tokenize("unit()")).unwrap()), Ok(Polynomial::constant(1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("unit")).unwrap()), Ok(Polynomial::constant(1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("unit*2")).unwrap()), Ok(Polynomial::constant(2.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("2unit")).unwrap()), Ok(Polynomial::constant(2.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("unit(2)")).unwrap()), Err(EvaluationError::MultipleExpressions));
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

    assert_eq!(evaluator.process(parser.process(tokenize("mod(17, 4)")).unwrap()), Ok(Polynomial::constant(1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("mod(1)")).unwrap()), Err(EvaluationError::ArgumentMissing("mod".to_string(), 2, 0)));
    assert_eq!(evaluator.process(parser.process(tokenize("mod(1, 2, 3)")).unwrap()), Err(EvaluationError::MultipleExpressions));
  }

  #[test]
  fn test_multiple_expression() {
    let evaluator = Evaluator::new();
    let parser = Parser::new();

    assert_eq!(evaluator.process(parser.process(tokenize("2, 2")).unwrap()), Err(EvaluationError::MultipleExpressions));
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

    assert_eq!(evaluator.process(parser.process(tokenize("x")).unwrap()), Ok(Polynomial::linear(0.0, 1.0)));
    assert_eq!(evaluator.process(parser.process(tokenize("x*x")).unwrap()), Ok(Polynomial::new(&[0.0, 0.0, 1.0])));
    assert_eq!(evaluator.process(parser.process(tokenize("x+x")).unwrap()), evaluator.process(parser.process(tokenize("2x")).unwrap()));
  }
}
