extern crate xxcalc;

use xxcalc::linear_solver::LinearSolver;
use xxcalc::calculator::Calculator;

fn main() {
  println!("The result is {}", LinearSolver.process("2+2").unwrap());
}