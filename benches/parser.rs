#![feature(test)]
extern crate test;
extern crate xxcalc;

#[cfg(test)]
mod benchmarks {
  use xxcalc::parser::*;
  use xxcalc::StringProcessor;
  use xxcalc::TokensProcessor;
  use xxcalc::tokenizer::*;
  use test::Bencher;

  pub fn add_sub_gen(n: usize) -> String {
    (0..n).map(|x| format!("{}-{}+", x, x).to_string()).fold(String::new(), |a, x| a+&x)+"0"
  }

  #[bench]
  #[ignore]
  fn bench_parser(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process(add_sub_r);
    let mut parser = Parser::default();
    parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
    parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));

    b.bytes = add_sub_r.len() as u64 * 10 * 4;
    b.iter(|| {
      (0..10).fold(0, |a, x| a + x + parser.process(tokens).unwrap().tokens.len())
    });
  }

  #[bench]
  fn bench_simple_expression(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process("2+2");
    let mut parser = Parser::default();
    parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));

    b.bytes = 3 * 4;
    b.iter(|| {
       parser.process(tokens).unwrap().tokens.len()
    });
  }

  #[bench]
  fn bench_function_call(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process("foo(2, 2)");
    let mut parser = Parser::default();

    b.bytes = 9 * 4;
    b.iter(|| {
       parser.process(tokens).unwrap().tokens.len()
    });
  }

  #[bench]
  #[ignore]
  fn bench_parser_without_arena(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();
    let tokens = tokenizer.process(add_sub_r);

    b.bytes = add_sub_r.len() as u64 * 10 * 4;
    b.iter(|| {
      (0..10).fold(0, |a, x| {
        let mut parser = Parser::default();
        parser.register_operator('+', Operator::new(1, OperatorAssociativity::Left));
        parser.register_operator('-', Operator::new(1, OperatorAssociativity::Left));
        a + x + parser.process(tokens).unwrap().tokens.len()
      })
    });
  }
}
