use tokenizer::{Tokens, Token, TokenList, Identifiers};
use std::collections::BTreeMap;

#[derive(PartialEq)]
pub enum OperatorAssociativity {
  Left,
  Right
}

pub struct Operator(i64, OperatorAssociativity);

impl Operator {
  pub fn new(p: i64, a: OperatorAssociativity) -> Operator {
    Operator(p, a)
  }
}

pub struct Parser {
  operators: BTreeMap<char, Operator>,
  output: Tokens
}

#[derive(Debug, PartialEq)]
pub enum ParsingError {
  UnknownOperator(char, usize),
  UnknownToken(usize),
  MissingBracket(usize),
  EmptyExpression
}

impl Default for Parser {
  fn default() -> Parser {
    Parser::new()
  }
}

pub trait TokensProcessor {
  fn process(&mut self, tokens: &Tokens) -> Result<&Tokens, ParsingError>;
}

impl TokensProcessor for Parser {
  fn process(&mut self, tokens_with_identifiers: &Tokens) -> Result<&Tokens, ParsingError> {
    let mut stack = TokenList::with_capacity(4);
    let &Tokens(ref tokens, ref identifiers) = tokens_with_identifiers;
    let mut iter = tokens.iter().peekable();

   self.output.0.clear();
   self.output.1 = identifiers.clone();

    while let Some(&(position, ref token)) = iter.next() {
      match *token {
        Token::BracketOpening => stack.push((position, token.clone())),
        Token::Number(_) => self.output.0.push((position, token.clone())),
        Token::Identifier(_) => {
          if let Some(&&(_, Token::BracketOpening)) = iter.peek() {
            stack.push((position, token.clone()));
          } else {
            self.output.0.push((position, token.clone()));
          }
        },
        Token::Separator => {
          while !stack.is_empty() {
            match stack.last() {
              Some(&(_, Token::BracketOpening)) => break,
              Some(_) => self.output.0.push(stack.pop().unwrap()),
              _ => break
            }
          }
        },
        Token::Operator(name) => {
          while !stack.is_empty() {
            match stack.last() {
              Some(&(_, Token::Operator(_))) | Some(&(_, Token::Identifier(_))) => {
                if self.lower_precedence(&token, &stack.last().unwrap().1) {
                  self.output.0.push(stack.pop().unwrap());
                } else {
                  break;
                }
              },
              _ => break
            }
          }

          if let Some(_) = self.operators.get(&name) {
            stack.push((position, token.clone()));
          } else {
            return Err(ParsingError::UnknownOperator(name, position));
          }
        },
        Token::BracketClosing => {
          let mut found = false;

          while !stack.is_empty() {
            match stack.last() {
              Some(&(_, Token::BracketOpening)) => {
                found = true;
                stack.pop();
                break;
              },
              _ => self.output.0.push(stack.pop().unwrap())
            }
          }

          if !found {
            return Err(ParsingError::MissingBracket(position));
          }
        },
        _ => return Err(ParsingError::UnknownToken(position))
      }
    }

    while !stack.is_empty() {
      match stack.last() {
        Some(&(position, Token::BracketOpening)) => return Err(ParsingError::MissingBracket(position)),
        Some(_) => self.output.0.push(stack.pop().unwrap()),
        _ => unreachable!()
      }
    }

    if self.output.0.is_empty() {
      return Err(ParsingError::EmptyExpression);
    }

    Ok(&self.output)
  }
}

impl Parser {
  pub fn new() -> Parser {
    Parser {
      operators: BTreeMap::new(),
      output: Tokens(TokenList::with_capacity(10), Identifiers::new())
    }
  }

  pub fn register_operator(&mut self, name: char, operator: Operator) -> Option<Operator> {
    self.operators.insert(name, operator)
  }

  #[inline(always)]
  fn lower_precedence(&self, a: &Token, b: &Token) -> bool {
    let &Operator(a_prec, ref a_assoc) = match *a {
      Token::Operator(name) => self.operators.get(&name).unwrap(),
      Token::Identifier(_) => return false,
      _ => unreachable!()
    };

    let &Operator(b_prec, _) = match *b {
      Token::Operator(name) => self.operators.get(&name).unwrap(),
      Token::Identifier(_) => return true,
      _ => unreachable!()
    };

    return (*a_assoc == OperatorAssociativity::Left && a_prec <= b_prec) ||
           (*a_assoc == OperatorAssociativity::Right && a_prec < b_prec);
  }
}

#[cfg(test)]
mod tests {
  use parser::*;
  use tokenizer::*;

  #[test]
  fn test_operator_registration() {
    let mut parser = Parser::new();

    // assert_eq!(parser.process(tokenize_ref!("2=2")), Err(ParsingError::UnknownOperator('=', 1)));

    parser.register_operator('=', Operator(-1, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("2=2")).unwrap().0.last().unwrap(), &(1, Token::Operator('=')));
  }

  #[test]
  fn test_precedence_and_associativity() {
    let mut parser = Parser::new();

    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('-', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));
    parser.register_operator('/', Operator(5, OperatorAssociativity::Left));
    parser.register_operator('^', Operator(10, OperatorAssociativity::Right));

    assert_eq!(parser.process(tokenize_ref!("2+2*2")).unwrap().0.last().unwrap(), &(1, Token::Operator('+')));
    assert_eq!(parser.process(tokenize_ref!("2*2+2")).unwrap().0.last().unwrap(), &(3, Token::Operator('+')));
    assert_eq!(parser.process(tokenize_ref!("2*2/2")).unwrap().0.last().unwrap(), &(3, Token::Operator('/')));
    assert_eq!(parser.process(tokenize_ref!("2/2*2")).unwrap().0.last().unwrap(), &(3, Token::Operator('*')));
    assert_eq!(parser.process(tokenize_ref!("2*2^2")).unwrap().0.last().unwrap(), &(1, Token::Operator('*')));
    assert_eq!(parser.process(tokenize_ref!("2^2*2")).unwrap().0.last().unwrap(), &(3, Token::Operator('*')));

    assert_eq!(parser.process(tokenize_ref!("2+2+2")).unwrap().0.iter().rev().skip(1).next().unwrap(), &(4, Token::Number(2.0)));
    assert_eq!(parser.process(tokenize_ref!("2^2^2")).unwrap().0.iter().rev().skip(1).next().unwrap(), &(3, Token::Operator('^')));
  }

  #[test]
  fn test_symbols() {
    let mut parser = Parser::new();
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("x")).unwrap().0.first().unwrap(), &(0, Token::Identifier(0)));
    assert_eq!(parser.process(tokenize_ref!("foobar")).unwrap().0.first().unwrap(), &(0, Token::Identifier(0)));

    assert_eq!(parser.process(tokenize_ref!("2x")).unwrap().0.len(), 3);
    assert_eq!(parser.process(tokenize_ref!("2x")).unwrap().0.last().unwrap(), &(0, Token::Operator('*')));
  }

  #[test]
  fn test_brackets() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize_ref!("2+2*2")).unwrap().0.last().unwrap(), &(1, Token::Operator('+')));
    assert_eq!(parser.process(tokenize_ref!("(2+2)*2")).unwrap().0.last().unwrap(), &(5, Token::Operator('*')));

    assert_eq!(parser.process(tokenize_ref!("2(14+2)")).unwrap().0.last().unwrap(), &(0, Token::Operator('*')));

    assert_eq!(parser.process(tokenize_ref!("(((2)))")).unwrap().0.first().unwrap(), &(3, Token::Number(2.0)));
    assert_eq!(parser.process(tokenize_ref!("(((2))+2)")).unwrap().0.last().unwrap(), &(6, Token::Operator('+')));
  }

  #[test]
  fn test_missing_brackets() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    // assert_eq!(parser.process(tokenize_ref!("2+(2(2+2)")), Err(ParsingError::MissingBracket(2)));
    // assert_eq!(parser.process(tokenize_ref!("(2(2+2)")), Err(ParsingError::MissingBracket(0)));
    // assert_eq!(parser.process(tokenize_ref!("2(2+2))")), Err(ParsingError::MissingBracket(6)));
  }

  #[test]
  fn test_empty_expression() {
    let mut parser = Parser::new();

    // assert_eq!(parser.process(tokenize_ref!("")), Err(ParsingError::EmptyExpression));
    // assert_eq!(parser.process(tokenize_ref!("((()))")), Err(ParsingError::EmptyExpression));
  }

  #[test]
  fn test_unknown_tokens() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    // assert_eq!(parser.process(tokenize_ref!("@2")), Err(ParsingError::UnknownToken(0)));
    // assert_eq!(parser.process(tokenize_ref!("2+2*{2+2}")), Err(ParsingError::UnknownToken(4)));
  }

  #[test]
  fn test_arguments() {
    let mut parser = Parser::new();

    assert_eq!(parser.process(tokenize_ref!("foo()")).unwrap().0.len(), 1);
    assert_eq!(parser.process(tokenize_ref!("foo(1)")).unwrap().0.len(), 2);
    assert_eq!(parser.process(tokenize_ref!("foo(1, 2)")).unwrap().0.len(), 3);
    assert_eq!(parser.process(tokenize_ref!("foo(1, 2)")).unwrap().0.last().unwrap(), &(0, Token::Identifier(0)));
    assert_eq!(parser.process(tokenize_ref!("foo(-1, 2)")).unwrap().0.first().unwrap(), &(4, Token::Number(-1.0)));
  }
}

#[cfg(test)]
mod benchmarks {
  use super::*;
  use tokenizer::*;
  use tokenizer::benchmarks::add_sub_gen;
  use test::Bencher;

  #[bench]
  #[ignore]
  fn bench_parser(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process(add_sub_r);
    let mut parser = Parser::default();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('-', Operator(1, OperatorAssociativity::Left));

    b.iter(|| {
      (0..10).fold(0, |a, x| a + x + parser.process(tokens).unwrap().0.len())
    });
  }

  #[bench]
  fn bench_simple_expression(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process("2+2");
    let mut parser = Parser::default();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));

    b.iter(|| {
       parser.process(tokens).unwrap().0.len()
    });
  }

  #[bench]
  fn bench_function_call(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process("foo(2, 2)");
    let mut parser = Parser::default();

    b.iter(|| {
       parser.process(tokens).unwrap().0.len()
    });
  }

  #[bench]
  #[ignore]
  fn bench_parser_without_arena(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process(add_sub_r);

    b.iter(|| {
      (0..10).fold(0, |a, x| {
        let mut parser = Parser::default();
        parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
        parser.register_operator('-', Operator(1, OperatorAssociativity::Left));
        a + x + parser.process(tokens).unwrap().0.len()
      })
    });
  }
}
