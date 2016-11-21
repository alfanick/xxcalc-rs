#[derive(Debug, Clone)]
pub struct Polynomial {
  coefficients: Vec<f64>
}

impl Polynomial {
  pub fn new(c: &[f64]) -> Polynomial {
    Polynomial {
      coefficients: c.to_vec()
    }
  }

  pub fn linear(b: f64, a: f64) -> Polynomial {
    Polynomial::new(&[b, a])
  }

  pub fn constant(b: f64) -> Polynomial {
    Polynomial::new(&[b])
  }

  pub fn zero() -> Polynomial {
    Polynomial::constant(0.0)
  }

  pub fn degree(&self) -> usize {
    self.coefficients.iter()
                     .rposition(|&a| a != 0.0)
                     .unwrap_or(0)
  }

  pub fn bind(&self, x: f64) -> Polynomial {
    let mut result: f64 = 0.0;

    for &coefficient in self.coefficients.iter().rev() {
      result *= x;
      result += coefficient;
    }

    Polynomial::constant(result)
  }

  pub fn as_f64(&self) -> Result<f64, PolynomialError> {
    match self.degree() {
      0 => Ok(self.coefficients[0]),
      _ => Err(PolynomialError::NonConstantError)
    }
  }

  pub fn as_string(&self, name: &str) -> String {
    self.coefficients.iter().enumerate().rev()
                     .filter_map(|(exponent, &coefficient)| {
                       if coefficient == 0.0 && exponent > 0 {
                         None
                       } else {
                         match exponent {
                           0 => Some(coefficient.to_string()),
                           1 => Some(format!("{}{}", coefficient, name)),
                           _ => Some(format!("{}{}^{}", coefficient, name, exponent))
                         }
                       }
                     })
                     .fold(String::with_capacity(self.coefficients.len() * 5), |mut expr, x| {
                       if !x.starts_with('-') && !expr.is_empty() {
                         expr.push('+');
                       }

                       expr.push_str(&x); expr
                     })
  }
}

impl Default for Polynomial {
  fn default() -> Polynomial {
    Polynomial::zero()
  }
}

use std::fmt;

impl fmt::Display for Polynomial {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.write_str(self.as_string("x").as_str())
  }
}

use std::ops::*;

impl Index<usize> for Polynomial {
  type Output = f64;

  fn index(&self, idx: usize) -> &f64 {
    &self.coefficients[idx]
  }
}

impl IndexMut<usize> for Polynomial {
  fn index_mut(&mut self, idx: usize) -> &mut f64 {
    self.coefficients.resize(idx + 1, 0.0);

    &mut self.coefficients[idx]
  }
}

impl AddAssign for Polynomial {
  fn add_assign(&mut self, other: Polynomial) {
    if other.coefficients.len() > self.coefficients.len() {
      self.coefficients.resize(other.coefficients.len(), 0.0);
    }

    for (idx, &coefficient) in other.coefficients.iter().enumerate() {
      self.coefficients[idx] += coefficient;
    }
  }
}

impl Add for Polynomial {
  type Output = Polynomial;

  fn add(mut self, other: Polynomial) -> Polynomial {
    self += other;
    self
  }
}

// impl Add for &'static Polynomial {
  // type Output = Polynomial;
//
  // fn add(mut self, other: &Polynomial) -> Polynomial {
    // let mut k = *self;
    // k += *other;
    // k
  // }
// }

impl SubAssign for Polynomial {
  fn sub_assign(&mut self, other: Polynomial) {
    if other.coefficients.len() > self.coefficients.len() {
      self.coefficients.resize(other.coefficients.len(), 0.0);
    }

    for (idx, &coefficient) in other.coefficients.iter().enumerate() {
      self.coefficients[idx] -= coefficient;
    }
  }
}

impl Sub for Polynomial {
  type Output = Polynomial;

  fn sub(mut self, other: Polynomial) -> Polynomial {
    self -= other;
    self
  }
}

impl MulAssign for Polynomial {
  fn mul_assign(&mut self, other: Polynomial) {
    let self_degree = self.degree();
    let other_degree = other.degree();

    if self_degree == 0 && other_degree == 0 {
      self.coefficients[0] *= other.coefficients[0];
    } else {
      let mut c = Vec::new();
      c.resize(self_degree + other_degree + 1, 0.0);

      for a in 0..self_degree+1 {
        for b in 0..other_degree+1 {
          c[a+b] += self.coefficients[a] * other.coefficients[b];
        }
      }

      self.coefficients = c;
    }
  }
}

impl Mul for Polynomial {
  type Output = Polynomial;

  fn mul(mut self, other: Polynomial) -> Polynomial {
    self *= other;
    self
  }
}

impl MulAssign<f64> for Polynomial {
  fn mul_assign(&mut self, other: f64) {
    let self_degree = self.degree();

    if self_degree == 0 {
      self.coefficients[0] *= other;
    } else {
      for idx in 0..self_degree+1 {
        self.coefficients[idx] *= other;
      }
    }
  }
}

impl DivAssign for Polynomial {
  fn div_assign(&mut self, other: Polynomial) {
    let mut self_degree = self.degree();
    let other_degree = other.degree();

    if self_degree < other_degree {
      panic!("Cannot perform polynomial division - divident is of smaller degree than divisor");
    } else
    if other_degree == 0 {
      if other.coefficients[0] == 0.0 && self_degree > 0 {
        panic!("Cannot perform polynomial division - divisor is zero");
      }

      for idx in 0..self_degree+1 {
        self.coefficients[idx] /= other.coefficients[0];
      }
    } else {
      let mut q = Polynomial::zero();
      q.coefficients.resize(other_degree - other_degree + 2, 0.0);

      while self_degree >= other_degree {
        let mut d = Polynomial::zero();
        let diff = self_degree - other_degree;
        d.coefficients.resize(other_degree + diff + 1, 0.0);
        for (idx, &coefficient) in other.coefficients.iter().enumerate() {
          d.coefficients[idx + diff] = coefficient;
        }
        q.coefficients[diff] = self.coefficients[self_degree] / d.coefficients[self_degree];
        d *= q.coefficients[diff];
        self.sub_assign(d);
        self_degree -= 1;
      }

      self.coefficients = q.coefficients;
    }
  }
}

impl Div for Polynomial {
  type Output = Polynomial;

  fn div(mut self, other: Polynomial) -> Polynomial {
    self /= other;
    self
  }
}

use std::cmp::{PartialEq, Eq};

impl PartialEq for Polynomial {
  fn eq(&self, other: &Polynomial) -> bool {
    let self_degree = self.degree();

    if other.degree() == self_degree {
      other.coefficients[0 .. self_degree+1] == self.coefficients[0 .. self_degree+1]
    } else {
      false
    }
  }
}

impl Eq for Polynomial { }

#[derive(Debug, PartialEq)]
pub enum PolynomialError {
  NonConstantError
}

#[cfg(test)]
mod tests {
  use polynomial::*;

  #[test]
  fn test_initialization() {
    assert_eq!(Polynomial::new(&[1.0, 2.0, 0.0]).coefficients, &[1.0, 2.0, 0.0]);
    assert_eq!(Polynomial::linear(1.0, 2.0).coefficients, &[1.0, 2.0]);
    assert_eq!(Polynomial::constant(3.14).coefficients, &[3.14]);
    assert_eq!(Polynomial::zero().coefficients, &[0.0]);
  }

  #[test]
  fn test_degree() {
    assert_eq!(Polynomial::zero().degree(), 0);
    assert_eq!(Polynomial::constant(1.0).degree(), 0);
    assert_eq!(Polynomial::linear(1.0, 0.0).degree(), 0);
    assert_eq!(Polynomial::linear(1.0, 1.0).degree(), 1);
    assert_eq!(Polynomial::new(&[1.0, 0.0, 1.0]).degree(), 2);
  }

  #[test]
  fn test_casting() {
    assert_eq!(Polynomial::zero().as_f64(), Ok(0.0));
    assert_eq!(Polynomial::constant(3.14).as_f64(), Ok(3.14));
    assert_eq!(Polynomial::linear(1.0, 1.0).as_f64(), Err(PolynomialError::NonConstantError));
    assert_eq!(Polynomial::linear(0.0, 1.0).as_f64(), Err(PolynomialError::NonConstantError));
  }

  #[test]
  fn test_string_conversion() {
    assert_eq!(Polynomial::zero().as_string("x"), "0");
    assert_eq!(Polynomial::constant(1.0).as_string("x"), "1");
    assert_eq!(Polynomial::linear(1.0, 2.0).as_string("x"), "2x+1");
    assert_eq!(Polynomial::linear(1.0, 2.0).as_string("z"), "2z+1");
    assert_eq!(Polynomial::new(&[1.0, 0.0, 2.0]).as_string("x"), "2x^2+1");
    assert_eq!(Polynomial::linear(-1.0, 2.0).as_string("x"), "2x-1");
    assert_eq!(Polynomial::new(&[1.0, 0.0, -2.0]).as_string("x"), "-2x^2+1");
    assert_eq!(Polynomial::new(&[-1.0, 0.0, -2.0]).as_string("x"), "-2x^2-1");
  }

  #[test]
  fn test_indexing() {
    assert_eq!(Polynomial::zero()[0], 0.0);
    assert_eq!(Polynomial::linear(0.0, 1.0)[1], 1.0);

    let mut x = Polynomial::zero();
    x[1] = 2.0;
    assert_eq!(x[0], 0.0);
    assert_eq!(x[1], 2.0);
  }

  #[test]
  #[should_panic]
  fn test_indexing_fail() {
    assert_eq!(Polynomial::zero()[1], 0.0);
  }

  #[test]
  fn test_bind() {
    assert_eq!(Polynomial::constant(1.0).bind(2.0).as_f64(), Ok(1.0));
    assert_eq!(Polynomial::linear(0.0, 1.0).bind(2.0).as_f64(), Ok(2.0));
    assert_eq!(Polynomial::new(&[0.0, 0.0, 1.0]).bind(2.0).as_f64(), Ok(4.0));
    assert_eq!(Polynomial::new(&[0.0, 0.0, 2.0]).bind(2.0).as_f64(), Ok(8.0));
    assert_eq!(Polynomial::new(&[1.0, 0.0, 2.0]).bind(2.0).as_f64(), Ok(9.0));
  }

  #[test]
  fn test_assign_add() {
    let mut a = Polynomial::constant(1.0);

    a += Polynomial::new(&[1.0, 2.0, 3.0]);

    assert_eq!(a[0], 2.0);
    assert_eq!(a[1], 2.0);
    assert_eq!(a[2], 3.0);
  }

  #[test]
  fn test_assign_sub() {
    let mut a = Polynomial::constant(1.0);

    a -= Polynomial::new(&[1.0, 2.0, 3.0]);

    assert_eq!(a[0], 0.0);
    assert_eq!(a[1], -2.0);
    assert_eq!(a[2], -3.0);
  }

  #[test]
  fn test_assign_mul() {
    let mut a = Polynomial::new(&[5.0, 0.0, 10.0, 6.0]);
    let b = Polynomial::new(&[1.0, 2.0, 4.0]);

    a *= b;

    assert_eq!(a[0], 5.0);
    assert_eq!(a[1], 10.0);
    assert_eq!(a[2], 30.0);
    assert_eq!(a[3], 26.0);
    assert_eq!(a[4], 52.0);
    assert_eq!(a[5], 24.0);

    let mut a = Polynomial::constant(2.0);
    let b = Polynomial::constant(4.0);

    a *= b;

    assert_eq!(a.as_f64(), Ok(8.0));

    let mut a = Polynomial::linear(1.0, 2.0);

    a *= 5.0;

    assert_eq!(a[0], 5.0);
    assert_eq!(a[1], 10.0);
  }

  #[test]
  fn test_assign_div() {
    let mut a = Polynomial::new(&[-10.0, -3.0, 1.0]);
    let b = Polynomial::linear(2.0, 1.0);

    a /= b;

    assert_eq!(a.degree(), 1);
    assert_eq!(a[0], -5.0);
    assert_eq!(a[1], 1.0);

    let mut a = Polynomial::constant(5.0);
    let b = Polynomial::constant(0.0);

    a /= b;

    assert_eq!(a.degree(), 0);
    assert!(a[0].is_infinite());
  }

  #[test]
  #[should_panic]
  fn test_assign_div_wrong_degree() {
    let mut a = Polynomial::linear(-5.0, 1.0);
    let b = Polynomial::new(&[1.0, 2.0, 3.0, 4.0]);

    a /= b;
  }

  #[test]
  #[should_panic]
  fn test_assign_div_zero_division() {
    let mut a = Polynomial::linear(-5.0, 1.0);
    let b = Polynomial::constant(0.0);

    a /= b;
  }

  #[test]
  fn test_equality() {
    assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0]), Polynomial::new(&[1.0, 2.0, 3.0]));
    assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0, 0.0]), Polynomial::new(&[1.0, 2.0, 3.0]));
    assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0]), Polynomial::new(&[1.0, 2.0, 3.0, 0.0]));
    assert!(Polynomial::new(&[1.0, 2.0, 3.0]) != Polynomial::new(&[1.0, 2.0, 3.0, 4.0]));
    assert!(Polynomial::new(&[1.0, 2.0, 3.0, 4.0]) != Polynomial::new(&[1.0, 2.0, 3.0]));
  }

  #[test]
  fn test_operations() {
    assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0]) + Polynomial::new(&[3.0, 2.0, 1.0]), Polynomial::new(&[4.0, 4.0, 4.0]));
    assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0]) - Polynomial::new(&[1.0, 2.0, 3.0]), Polynomial::zero());
    assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0]) * Polynomial::constant(2.0), Polynomial::new(&[2.0, 4.0, 6.0]));
    assert_eq!(Polynomial::constant(2.0) * Polynomial::linear(0.0, 1.0), Polynomial::linear(0.0, 2.0));
    assert!((Polynomial::constant(2.0) / Polynomial::constant(0.0)).as_f64().unwrap().is_infinite());
    assert_eq!(Polynomial::constant(2.0) / Polynomial::constant(2.0), Polynomial::constant(1.0));
    assert_eq!(Polynomial::linear(0.0, 2.0) / Polynomial::linear(0.0, 1.0), Polynomial::constant(2.0));
    assert_eq!(Polynomial::linear(0.0, 1.0) / Polynomial::linear(0.0, 2.0), Polynomial::constant(0.5));
  }
}