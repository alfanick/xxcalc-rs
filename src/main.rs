extern crate xxcalc;
use xxcalc::calculator::Calculator;
use xxcalc::polynomial_calculator::PolynomialCalculator;

extern crate rustyline;
use rustyline::Editor;

fn main() {
  let mut rl = Editor::<()>::new();
  let _ = rl.load_history(".xxcalcrs_history");

  while let Ok(input) = rl.readline(">>> ") {
    rl.add_history_entry(&input);

    let result = PolynomialCalculator.process(&input);

    if let Ok(value) = result {
      println!("{}", value.as_string("x"));
    } else {
      println!("Error: {:?}", result);
    }
  }

  rl.save_history(".xxcalcrs_history").unwrap();
}
