use polynomial::Polynomial;
use tokenizer::{TokenList, Token};
use std::collections::BTreeMap;

#[derive(Debug, PartialEq)]
pub enum EvaluationError {
  UnknownSymbol(String, usize),
  ArgumentMissing(String, usize, usize),
  MultipleExpressions,
  ConflictingName(String)
}

pub trait TokensReducer {
  fn process(&self, tokens: TokenList) -> Result<Polynomial, EvaluationError>;
}

type FunctionHandle = Box<Fn(&[Polynomial]) -> Result<Polynomial, EvaluationError>>;

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

impl TokensReducer for Evaluator {
  fn process(&self, mut tokens: TokenList) -> Result<Polynomial, EvaluationError> {
    let mut stack: Vec<Polynomial> = Vec::with_capacity(tokens.len());

    while let Some((position, token)) = tokens.pop_front() {
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

  fn call_function(&self, name: &String, position: usize, stack: &mut Vec<Polynomial>) -> Result<Polynomial, EvaluationError> {
    if let Some(function) = self.functions.get(name) {
      if stack.len() < function.arity {
        Err(EvaluationError::ArgumentMissing(name.clone(), function.arity, position))
      } else {
        let old_stack_len = stack.len();
        let mut args: Vec<Polynomial> = Vec::with_capacity(function.arity);

        for _ in 0..function.arity {
          args.push(stack.pop().unwrap());
        }

        args.reverse();

        assert!(args.len() == function.arity);
        assert!(stack.len() == old_stack_len - function.arity);

        (function.handle)(&args)
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
mod test {
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

  fn addition(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() + args[1].clone())
  }

  fn subtraction(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
    Ok(args[0].clone() - args[1].clone())
  }

  fn multiplication(args: &[Polynomial]) -> Result<Polynomial, EvaluationError> {
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

    assert_eq!(evaluator.process(parser.process(tokenize("double(2)")).unwrap()), Err(EvaluationError::UnknownSymbol("double".to_string(), 0)));

    evaluator.register_function("double", Function::new(1, |args|{
      return Ok(args[0].clone() * 2.0)
    }));
  }
}