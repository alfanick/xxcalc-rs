#![feature(test)]
extern crate test;
extern crate xxcalc;

#[cfg(test)]
mod benchmarks {
  use xxcalc::polynomial_calculator::*;
  use xxcalc::TokensReducer;
  use xxcalc::TokensProcessor;
  use xxcalc::StringProcessor;
  use xxcalc::calculator::Calculator;
  use xxcalc::tokenizer::Tokenizer;
  use test::Bencher;

  pub fn add_sub_gen(n: usize) -> String {
    (0..n).map(|x| format!("{}-{}+", x, x).to_string()).fold(String::new(), |a, x| a+&x)+"0"
  }

  #[bench]
  #[ignore]
  fn bench_calculation(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);

    let mut tokenizer = Tokenizer::default();
    let mut parser = PolynomialParser::default().parser;
    let evaluator = PolynomialEvaluator::default().evaluator;

    b.iter(|| {
      (0..10).fold(0.0, |a, _| {
        let tokens = tokenizer.process(add_sub_r);
        let parsed_tokens = parser.process(tokens).unwrap();

        a + evaluator.process(parsed_tokens).unwrap()[0]
      })
    });
  }

  use std::iter::repeat;

  #[bench]
  #[ignore]
  fn bench_calculation_linear(b: &mut Bencher) {
    let add_sub_r: &String = &repeat("x-x+").take(100000).chain(repeat("0").take(1)).collect();

    let mut tokenizer = Tokenizer::default();
    let mut parser = PolynomialParser::default().parser;
    let evaluator = PolynomialEvaluator::default().evaluator;

    b.iter(|| {
      (0..10).fold(0.0, |a, _| {
        let tokens = tokenizer.process(add_sub_r);
        let parsed_tokens = parser.process(tokens).unwrap();

        a + evaluator.process(parsed_tokens).unwrap()[0]
      })
    });
  }

  #[bench]
  #[ignore]
  fn bench_calculation_constant(b: &mut Bencher) {
    let add_sub_r: &String = &repeat("pi-pi+").take(100000).chain(repeat("0").take(1)).collect();

    let mut tokenizer = Tokenizer::default();
    let mut parser = PolynomialParser::default().parser;
    let evaluator = PolynomialEvaluator::default().evaluator;

    b.iter(|| {
      (0..10).fold(0.0, |a, _| {
        let tokens = tokenizer.process(add_sub_r);
        let parsed_tokens = parser.process(tokens).unwrap();

        a + evaluator.process(parsed_tokens).unwrap()[0]
      })
    });
  }

  #[bench]
  #[ignore]
  fn bench_calculation_without_arena(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);

    b.iter(|| {
      (0..10).fold(0.0, |a, _| a + PolynomialCalculator.process(add_sub_r).unwrap()[0])
    });
  }
}
