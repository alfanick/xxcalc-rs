# xxcalc-rs [![Build Status](https://travis-ci.org/alfanick/xxcalc-rs.svg?branch=master)](https://travis-ci.org/alfanick/xxcalc-rs) [![Coverage Status](https://coveralls.io/repos/github/alfanick/xxcalc-rs/badge.svg?branch=master)](https://coveralls.io/github/alfanick/xxcalc-rs?branch=master) [![Rust Crate](https://img.shields.io/crates/v/xxcalc.svg)](https://crates.io/crates/xxcalc)

An embeddable or a standalone robust floating-point polynomial calculator written in Rust.

This project is a Rust crate (library) which provides a floating-point numbers calculator
in an easy to use API. Furthermore a basic unit of computation is a polynomial, so multiple
arithmetic operations can be done using `x` symbols.

You can use this library in your own projects as mathematical evaluator or as a standalone,
command line calculator by using `xxcalc` binary. Internally it uses hand-mande tokenizer and
a Dijskatra's shunting-yard algorithm to convert infix form into Reverse Polish Notation,
which is later evaluated. Please see the [complete documentation](https://alfanick.github.io/xxcalc-rs/xxcalc/index.html)
for the implementation details.

## Binary

`xxcalc` can be used to replace common `bc` Unix-utility. It has a support for addition,
subtraction, multiplication, division and exponentation built-in.

Here is an example session with the calculator:

```
>>> (3+(4-1))*5
30
>>> 2 * x + 0.5 = 1
0.25
>>> 2x + 1 = 2(1-x)
0.25
>>> (x^3+2x-1)^3
x^9+6x^7-3x^6+12x^5-12x^4+11x^3-12x^2+6x-1
>>> bind((x^3+2x-1)^3, 1)
8
>>> log(128, 2)
7
```

### Features

* `+`, `-`, `*`, `/`, `^` operators on floating-point polynomials
* scientific notation and negative numbers
* polynomials representation using `x` symbol
* solving linear equations solver using `=` operator
* `log(number, base)`, `log10(number)`, `bind(polynomial, x value)` built-in functions
* `pi` and `e` constants
* input read from stdin (can be used for piping)
* interactive readline-like mode with history

### Installation

You need Rust programming language environment (works with stable, beta and nighly channels).
If you don't have already installed please use [rustup.rs](https://www.rustup.rs) to easily
install the complete environment. Then you can install packaged version from the crates.io
using `cargo install xxcalc --features interactive`.

#### Compilation

The basic compilation process from the source is just running `cargo` in command line:

```bash
$ cargo build --release
$ ./target/release/xxcalc
2+2
4
```

Than you can copy the `xxcalc` binary wherever you prefer (like `/usr/local/bin`), however this
builds a non-interactive version of the binary, with no support for history completion.

In order to build the calculator with support for history (stored in `~/.xxcalcrs_history`),
you need it enable `interactive` feature (it will automatically resolve dependencies to
[`rustyline`](https://github.com/kkawakam/rustyline)):

```bash
$ cargo build --release --features interactive
$ ./target/release/xxcalc
>>> 2+2
4
```

### Benchmarks

Coming soon. It is at least 2.5 times faster than `bc` and incomparable quicker than
[GNU Octave](https://www.gnu.org/software/octave/).

## Library

The `xxcalc` calculator provides a clean and well documented API. Please see
[its documentation](https://alfanick.github.io/xxcalc-rs/xxcalc/index.html).

The library builds on stable, beta and nighly channels and require no additional dependencies,
unless interactive feature is enabled. Therefore you can easily add mathematical
expressions evaluator into your project.

The calculator is meant to be extensible -- you can register your own functions or constants.
You can even change tokenizer, parser or an evaluator into your own. Furthermore a `Polynomial`
is a standalone type which can be used in your projects without usage of other features of the
calculator.

### Usage

Add `xxcalc` as dependency in your `Cargo.toml`, than just use `xxcalc` crate and the
parts you need.

```
# Cargo.toml
[dependencies]
xxcalc = "0.2.0"
```

```rust
extern crate xxcalc;

use xxcalc::linear_solver::LinearSolver;
use xxcalc::calculator::Calculator;
use xxcalc::polynomial::Polynomial;

fn main() {
  println!("The result is {}", LinearSolver.process("2+2").unwrap());
}
```

Many usage hints and scenarios are available in
[the documentation](https://alfanick.github.io/xxcalc-rs/xxcalc/index.html).

### Tests

The projects is thoroughly unit tested, some examples are directly provided in the
documentation. Use `cargo test` to run the unit tests.

If you have a Rust nighly compiler you can run some built-in bencharks using `cargo bench`.
Some more extensive benchmarks (using large expressions) can be run using `carbo bench -- --ignored`.

# License

The project is licensed under MIT license, the author is Amadeusz Juskowiak <juskowiak@amadeusz.me>,
feel free to ask any questions or to hire me.
