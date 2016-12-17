#![feature(test)]
extern crate test;
extern crate xxcalc;

#[cfg(test)]
pub mod benchmarks {
  use xxcalc::tokenizer::*;
  use xxcalc::StringProcessor;
  use test::Bencher;

  pub fn add_sub_gen(n: usize) -> String {
    (0..n).map(|x| format!("{}-{}+", x, x).to_string()).fold(String::new(), |a, x| a+&x)+"0"
  }

  #[bench]
  #[ignore]
  fn bench_tokenizer(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);
    let mut tokenizer = Tokenizer::default();

    b.bytes = add_sub_r.len() as u64 * 10;

    b.iter(|| {
      (0..10).fold(0, |a, x| a + x + tokenizer.process(add_sub_r).tokens.len())
    });
  }

  #[bench]
  #[ignore]
  fn bench_tokenizer_without_arena(b: &mut Bencher) {
    let add_sub_r = &add_sub_gen(100000);

    b.bytes = add_sub_r.len() as u64 * 10;

    b.iter(|| {
      (0..10).fold(0, |a, x| {
        let mut tokenizer = Tokenizer::default();
        a + x + tokenizer.process(add_sub_r).tokens.len()
      })
    });
  }

  #[bench]
  fn bench_tokenizer_numbers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.bytes = 18;

    b.iter(|| {
      tokenizer.process("3.1415926535897932").tokens.len()
    });
  }

  #[bench]
  fn bench_tokenizer_short_numbers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.bytes = 1;

    b.iter(|| {
      tokenizer.process("2").tokens.len()
    });
  }

  #[bench]
  fn bench_tokenizer_identifiers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.bytes = 18;

    b.iter(|| {
      tokenizer.process("_lorem_ipsum_dolor").tokens.len()
    });
  }

  #[bench]
  fn bench_tokenizer_short_identifiers(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.bytes = 1;

    b.iter(|| {
      tokenizer.process("x").tokens.len()
    });
  }

  #[bench]
  fn bench_tokenizer_brackets(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.bytes = 1;

    b.iter(|| {
      tokenizer.process("(").tokens.len()
    });
  }

  #[bench]
  fn bench_tokenizer_operators(b: &mut Bencher) {
    let mut tokenizer = Tokenizer::default();

    b.bytes = 1;

    b.iter(|| {
      tokenizer.process("+").tokens.len()
    });
  }
}
