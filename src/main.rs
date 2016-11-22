extern crate xxcalc;
use xxcalc::tokenizer::{StringProcessor, Tokenizer};
use xxcalc::parser::TokensProcessor;
use xxcalc::evaluator::TokensReducer;
use xxcalc::linear_solver::{LinearSolverParser, LinearSolverEvaluator};

extern crate rustyline;
use rustyline::Editor;

fn main() {
  let mut rl = Editor::<()>::new();
  let _ = rl.load_history(".xxcalcrs_history");

  let mut tokenizer = Tokenizer::default();
  let mut parser = LinearSolverParser::default().parser;
  let evaluator = LinearSolverEvaluator::default().evaluator;

  while let Ok(input) = rl.readline(">>> ") {
    if input.len() < 1024 {
      rl.add_history_entry(&input);
    }

    let tokens = tokenizer.process(&input);
    match parser.process(tokens) {
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
