extern crate xxcalc;

#[cfg(not(feature = "interactive"))]
fn main() {
  non_interactive::main();
}

#[cfg(feature = "interactive")]
fn main() {
  interactive::main();
}

#[cfg(not(feature = "interactive"))]
mod non_interactive {
  use xxcalc::{StringProcessor, TokensProcessor, TokensReducer};
  use xxcalc::tokenizer::Tokenizer;
  use xxcalc::linear_solver::{LinearSolverParser, LinearSolverEvaluator};

  use std::io::{self, BufRead};

  pub fn main() {
    let mut input = String::new();
    let stdin = io::stdin();

    let mut tokenizer = Tokenizer::default();
    let mut parser = LinearSolverParser::default().parser;
    let evaluator = LinearSolverEvaluator::default().evaluator;

    while let Ok(n) = stdin.lock().read_line(&mut input) {
      if n == 0 {
        break;
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

      input.clear();
    }
  }
}

#[cfg(feature = "interactive")]
mod interactive {
  use xxcalc::{StringProcessor, TokensProcessor, TokensReducer};
  use xxcalc::tokenizer::Tokenizer;
  use xxcalc::linear_solver::{LinearSolverParser, LinearSolverEvaluator};

  extern crate rustyline;
  use self::rustyline::Editor;
  use std::env;

  pub fn main() {
    let mut rl = Editor::<()>::new();
    let _ = rl.load_history(&history_file());

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

    rl.save_history(&history_file()).unwrap();
  }

  fn history_file() -> String {
    if let Some(mut path) = env::home_dir() {
      path.push(".xxcalcrs_history");
      path.to_string_lossy().into_owned()
    } else {
      String::from(".xxcalcrs_history")
    }
  }
}