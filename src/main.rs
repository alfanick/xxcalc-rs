extern crate xxcalc;
use xxcalc::tokenizer::tokenize;
use xxcalc::parser::TokensProcessor;
use xxcalc::evaluator::TokensReducer;
use xxcalc::polynomial_calculator::PolynomialParser;
use xxcalc::polynomial_calculator::PolynomialEvaluator;

extern crate rustyline;
use rustyline::Editor;

fn main() {
  let mut rl = Editor::<()>::new();
  let _ = rl.load_history(".xxcalcrs_history");

  let parser = PolynomialParser::default().parser;
  let evaluator = PolynomialEvaluator::default().evaluator;

  while let Ok(input) = rl.readline(">>> ") {
    rl.add_history_entry(&input);

    match parser.process(tokenize(&input)) {
      Ok(t) => {
        match evaluator.process(t) {
          Ok(result) => println!("{}", result.as_string("x")),
          Err(e) => println!("Evaluation error: {:?}", e)
        }
      },
      Err(e) => println!("Parsing error: {:?}", e)
    }
  }

  rl.save_history(".xxcalcrs_history").unwrap();
}
