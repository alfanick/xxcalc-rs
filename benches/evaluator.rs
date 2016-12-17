#![feature(test)]
extern crate test;
extern crate xxcalc;

#[cfg(test)]
mod benchmarks {
  use xxcalc::evaluator::*;
  use xxcalc::TokensReducer;
  use xxcalc::TokensProcessor;
  use xxcalc::StringProcessor;
  use xxcalc::parser::{Parser, Operator, OperatorAssociativity};
  use xxcalc::tokenizer::{Tokenizer};
  use xxcalc::polynomial_calculator::functions::{addition, subtraction};
  use xxcalc::polynomial::Polynomial;
  use test::Bencher;

  pub fn add_sub_gen(n: usize) -> String {
    (0..n).map(|x| format!("{}-{}+", x, x).to_string()).fold(String::new(), |a, x| a+&x)+"0"
  }

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

    b.bytes = add_sub_r.len() as u64 * 10 * 4;

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

    b.bytes = add_sub_r.len() as u64 * 10 * 4;
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

    b.bytes = 4 * 4;
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

    b.bytes = 2 * 4;
    b.iter(|| {
      evaluator.process(parsed_tokens).unwrap()
    });
  }

}
