use tokenizer::{TokenList, Token};
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
  operators: BTreeMap<char, Operator>
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
  fn process(&self, tokens: &TokenList) -> Result<TokenList, ParsingError>;
}

impl TokensProcessor for Parser {
  fn process(&self, tokens: &TokenList) -> Result<TokenList, ParsingError> {
    let mut stack = TokenList::with_capacity(10);
    let mut output = TokenList::with_capacity(tokens.len());
    let mut iter = tokens.iter().peekable();

    while let Some(&(position, ref token)) = iter.next() {
      match *token {
        Token::BracketOpening => stack.push((position, token.clone())),
        Token::Number(_) => output.push((position, token.clone())),
        Token::Identifier(_) => {
          if let Some(&&(_, Token::BracketOpening)) = iter.peek() {
            stack.push((position, token.clone()));
          } else {
            output.push((position, token.clone()));
          }
        },
        Token::Separator => {
          while !stack.is_empty() {
            match stack.last() {
              Some(&(_, Token::BracketOpening)) => break,
              Some(_) => output.push(stack.pop().unwrap()),
              _ => break
            }
          }
        },
        Token::Operator(name) => {
          while !stack.is_empty() {
            match stack.last() {
              Some(&(_, Token::Operator(_))) | Some(&(_, Token::Identifier(_))) => {
                if self.lower_precedence(&token, &stack.last().unwrap().1) {
                  output.push(stack.pop().unwrap());
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
              _ => output.push(stack.pop().unwrap())
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
        Some(_) => output.push(stack.pop().unwrap()),
        _ => unreachable!()
      }
    }

    if output.is_empty() {
      return Err(ParsingError::EmptyExpression);
    }

    Ok(output)
  }
}

impl Parser {
  pub fn new() -> Parser {
    Parser {
      operators: BTreeMap::new()
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
  use tokenizer::{tokenize, Token};

  #[test]
  fn test_operator_registration() {
    let mut parser = Parser::new();

    assert_eq!(parser.process(tokenize("2=2")), Err(ParsingError::UnknownOperator('=', 1)));

    parser.register_operator('=', Operator(-1, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize("2=2")).unwrap().last().unwrap(), &(1, Token::Operator('=')));
  }

  #[test]
  fn test_precedence_and_associativity() {
    let mut parser = Parser::new();

    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('-', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));
    parser.register_operator('/', Operator(5, OperatorAssociativity::Left));
    parser.register_operator('^', Operator(10, OperatorAssociativity::Right));

    assert_eq!(parser.process(tokenize("2+2*2")).unwrap().last().unwrap(), &(1, Token::Operator('+')));
    assert_eq!(parser.process(tokenize("2*2+2")).unwrap().last().unwrap(), &(3, Token::Operator('+')));
    assert_eq!(parser.process(tokenize("2*2/2")).unwrap().last().unwrap(), &(3, Token::Operator('/')));
    assert_eq!(parser.process(tokenize("2/2*2")).unwrap().last().unwrap(), &(3, Token::Operator('*')));
    assert_eq!(parser.process(tokenize("2*2^2")).unwrap().last().unwrap(), &(1, Token::Operator('*')));
    assert_eq!(parser.process(tokenize("2^2*2")).unwrap().last().unwrap(), &(3, Token::Operator('*')));

    assert_eq!(parser.process(tokenize("2+2+2")).unwrap().iter().rev().skip(1).next().unwrap(), &(4, Token::Number(2.0)));
    assert_eq!(parser.process(tokenize("2^2^2")).unwrap().iter().rev().skip(1).next().unwrap(), &(3, Token::Operator('^')));
  }

  #[test]
  fn test_symbols() {
    let mut parser = Parser::new();
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize("x")).unwrap().first().unwrap(), &(0, Token::Identifier("x".to_string())));
    assert_eq!(parser.process(tokenize("foobar")).unwrap().first().unwrap(), &(0, Token::Identifier("foobar".to_string())));

    assert_eq!(parser.process(tokenize("2x")).unwrap().len(), 3);
    assert_eq!(parser.process(tokenize("2x")).unwrap().last().unwrap(), &(0, Token::Operator('*')));
  }

  #[test]
  fn test_brackets() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize("2+2*2")).unwrap().last().unwrap(), &(1, Token::Operator('+')));
    assert_eq!(parser.process(tokenize("(2+2)*2")).unwrap().last().unwrap(), &(5, Token::Operator('*')));

    assert_eq!(parser.process(tokenize("2(14+2)")).unwrap().last().unwrap(), &(0, Token::Operator('*')));

    assert_eq!(parser.process(tokenize("(((2)))")).unwrap().first().unwrap(), &(3, Token::Number(2.0)));
    println!("{:?}", tokenize("(((2))+2)"));
    println!("{:?}", parser.process(tokenize("(((2))+2)")));
    assert_eq!(parser.process(tokenize("(((2))+2)")).unwrap().last().unwrap(), &(6, Token::Operator('+')));
  }

  #[test]
  fn test_missing_brackets() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize("2+(2(2+2)")), Err(ParsingError::MissingBracket(2)));
    assert_eq!(parser.process(tokenize("(2(2+2)")), Err(ParsingError::MissingBracket(0)));
    assert_eq!(parser.process(tokenize("2(2+2))")), Err(ParsingError::MissingBracket(6)));
  }

  #[test]
  fn test_empty_expression() {
    let parser = Parser::new();

    assert_eq!(parser.process(tokenize("")), Err(ParsingError::EmptyExpression));
    assert_eq!(parser.process(tokenize("((()))")), Err(ParsingError::EmptyExpression));
  }

  #[test]
  fn test_unknown_tokens() {
    let mut parser = Parser::new();
    parser.register_operator('+', Operator(1, OperatorAssociativity::Left));
    parser.register_operator('*', Operator(5, OperatorAssociativity::Left));

    assert_eq!(parser.process(tokenize("@2")), Err(ParsingError::UnknownToken(0)));
    assert_eq!(parser.process(tokenize("2+2*{2+2}")), Err(ParsingError::UnknownToken(4)));
  }

  #[test]
  fn test_arguments() {
    let parser = Parser::new();

    assert_eq!(parser.process(tokenize("foo()")).unwrap().len(), 1);
    assert_eq!(parser.process(tokenize("foo(1)")).unwrap().len(), 2);
    assert_eq!(parser.process(tokenize("foo(1, 2)")).unwrap().len(), 3);
    assert_eq!(parser.process(tokenize("foo(1, 2)")).unwrap().last().unwrap(), &(0, Token::Identifier("foo".to_string())));
    assert_eq!(parser.process(tokenize("foo(-1, 2)")).unwrap().first().unwrap(), &(4, Token::Number(-1.0)));
  }
}
