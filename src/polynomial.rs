//! Defines Polynomial expression with basic operators on it.

/// Polynomial struct represents a mathematical concept of polynomials.
///
/// A polynomial is defined by real values of its coefficients corresponding
/// to natural-numbered powers of the variable x. As coefficients are represented
/// as continous vector, storing polynomials of high degree, but with most
/// terms empty is quite expensive (`x^1023` makes vector of size 1024).
///
/// As one can imagine `x^3.14` is not a polynomial, while `3.14x^2+2` is a
/// polynomial.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// assert_eq!(String::from(Polynomial::new(&[1.0])), "1");
/// assert_eq!(String::from(Polynomial::new(&[0.0, 1.0])), "x");
/// assert_eq!(String::from(Polynomial::new(&[2.0, 0.0, 3.14])), "3.14x^2+2");
/// ```
#[derive(Debug, Clone)]
pub struct Polynomial {
  /// Vector of coefficients for appropriate powers
  coefficients: Vec<f64>
}

impl Polynomial {
  /// Creates new polynomial from given coefficients
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0])[0], 1.0);
  /// assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0])[2], 3.0);
  /// ```
  #[inline(always)]
  pub fn new(c: &[f64]) -> Polynomial {
    Polynomial { coefficients: c.to_vec() }
  }

  /// Creates a linear polynomial (a polynomial of degree one).
  /// Such polynomial represents a linear expression `ax+b`.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::linear(1.0, 0.0), Polynomial::new(&[1.0, 0.0]));
  /// assert_eq!(Polynomial::linear(0.0, 1.0), Polynomial::new(&[0.0, 1.0]));
  /// ```
  #[inline(always)]
  pub fn linear(b: f64, a: f64) -> Polynomial {
    Polynomial { coefficients: vec![b, a] }
  }

  /// Creates a constant (degenerative) polynomial (a polynomial of
  /// degree zero).
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::constant(0.0), Polynomial::new(&[0.0]));
  /// assert_eq!(Polynomial::constant(3.14), Polynomial::new(&[3.14]));
  /// ```
  #[inline(always)]
  pub fn constant(b: f64) -> Polynomial {
    Polynomial { coefficients: vec![b] }
  }

  /// Creates a zero polynomial (a polynomial with constant 0.0). While
  /// the math does not define degree of such polynomial, for sake of
  /// usability, in this library such polynomial is defined with a degree zero.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::zero(), Polynomial::constant(0.0));
  /// assert_eq!(Polynomial::zero().degree(), 0);
  /// ```
  #[inline(always)]
  pub fn zero() -> Polynomial {
    Polynomial { coefficients: vec![0.0] }
  }

  /// Computes degree of the polynomial. This method has a linear
  /// complexity as degree is not stored precomputed.
  ///
  /// Degree is a largest power with non-zero coefficient, however
  /// a zero polynomial has a zero degree. It should be observed
  /// that size of coefficients vector may not be equal to the degree,
  /// as some of coefficients may be zero.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::zero().degree(), 0);
  /// assert_eq!(Polynomial::constant(0.0).degree(), 0);
  /// assert_eq!(Polynomial::linear(1.0, 0.0).degree(), 0);
  /// assert_eq!(Polynomial::linear(1.0, 1.0).degree(), 1);
  /// assert_eq!(Polynomial::new(&[1.0, 1.0, 1.0, 1.0]).degree(), 3);
  /// assert_eq!(Polynomial::new(&[1.0, 1.0, 1.0, 1.0, 0.0, 0.0]).degree(), 3);
  /// ```
  pub fn degree(&self) -> usize {
    self.coefficients.iter()
                     .rposition(|&a| a != 0.0)
                     .unwrap_or(0)
  }

  /// Computes value of the polynomial by binding the variable with
  /// given constant value.
  ///
  /// A Horner method is used for this computation to keep it linear
  /// and efficient.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::constant(3.0).bind(9.0), Polynomial::constant(3.0));
  /// assert_eq!(Polynomial::linear(0.0, 1.0).bind(2.0), Polynomial::constant(2.0));
  /// assert_eq!(Polynomial::linear(1.0, 4.0).bind(2.0), Polynomial::constant(9.0));
  /// assert_eq!(Polynomial::new(&[1.0, 4.0, 4.0]).bind(2.0), Polynomial::constant(25.0));
  /// ```
  pub fn bind(&self, x: f64) -> Polynomial {
    let mut result: f64 = 0.0;

    for &coefficient in self.coefficients.iter().rev() {
      result *= x;
      result += coefficient;
    }

    Polynomial::constant(result)
  }

  /// Tries to interpret polynomial as real value.
  ///
  /// Polynomial can be transformed to real value (double) only
  /// if its degree is zero (if the polynomial is constant),
  /// otherwise value of polynomial can be binded for particular
  /// value of variable.
  ///
  /// # Errors
  ///
  /// Will return `PolynomialError::NonConstantError` when the degree
  /// is greater than zero.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// # use xxcalc::polynomial::PolynomialError;
  /// assert_eq!(Polynomial::constant(3.0).as_f64(), Ok(3.0));
  /// assert_eq!(Polynomial::zero().as_f64(), Ok(0.0));
  /// assert_eq!(Polynomial::linear(1.0, 0.0).as_f64(), Ok(1.0));
  /// assert_eq!(Polynomial::linear(1.0, 1.0).as_f64(), Err(PolynomialError::NonConstantError));
  /// ```
  pub fn as_f64(&self) -> Result<f64, PolynomialError> {
    match self.degree() {
      0 => Ok(self.coefficients[0]),
      _ => Err(PolynomialError::NonConstantError)
    }
  }

  /// Returns human readable representation of the polynomial.
  /// Uses provided name as name of the variable.
  ///
  /// The returned string is as short as possible version of
  /// the polynomial starting with the largest exponents. Terms
  /// with empty coefficients are skipped, so as unnecessary
  /// symbols and exponents. In example `2x+1` is returned instead
  /// of `0*x^2+2*x^2+2*x^0`.
  ///
  /// # Examples
  ///
  /// ```
  /// # use xxcalc::polynomial::Polynomial;
  /// assert_eq!(Polynomial::new(&[0.0, 2.0]).as_string("x"), "2x");
  /// assert_eq!(Polynomial::new(&[-1.0, 2.0]).as_string("x"), "2x-1");
  /// assert_eq!(Polynomial::new(&[-1.0, 2.0, 4.0]).as_string("x"), "4x^2+2x-1");
  /// assert_eq!(Polynomial::new(&[-1.0, 2.0, 0.0, 4.0]).as_string("x"), "4x^3+2x-1");
  /// assert_eq!(Polynomial::new(&[-1.0, 2.0, 0.0, 4.0]).as_string("foo"), "4foo^3+2foo-1");
  /// ```
  pub fn as_string(&self, name: &str) -> String {
    self.coefficients.iter().enumerate().rev()
                     .filter_map(|(exponent, &coefficient)| {
                       if coefficient == 0.0 && exponent > 0 {
                         None
                       } else {
                         match exponent {
                           0 => Some(coefficient.to_string()),
                           _ if !coefficient.is_normal() => Some(format!("{}*{}^{}", coefficient, name, exponent)),
                           1 if coefficient == -1.0  => Some(format!("-{}", name)),
                           1 if coefficient == 1.0 => Some(format!("{}", name)),
                           1 if coefficient != 0.0 => Some(format!("{}{}", coefficient, name)),
                           _ if coefficient == -1.0 => Some(format!("-{}^{}", name, exponent)),
                           _ if coefficient == 1.0 => Some(format!("{}^{}", name, exponent)),
                           _ => Some(format!("{}{}^{}", coefficient, name, exponent))
                         }
                       }
                     })
                     .fold(String::with_capacity(self.coefficients.len() * 5), |mut expr, x| {
                       if !x.starts_with('-') && !expr.is_empty() {
                         if x == "0" {
                          return expr;
                         }
                        expr.push('+');
                       }

                       expr.push_str(&x); expr
                     })
  }
}

/// A zero polynomial is returned by default
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// assert_eq!(Polynomial::default(), Polynomial::zero());
/// ```
impl Default for Polynomial {
  #[inline(always)]
  fn default() -> Polynomial {
    Polynomial::zero()
  }
}

/// Makes string out of polynomial with `x` symbol
/// as a variable.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// assert_eq!(String::from(Polynomial::linear(1.0, 2.0)), "2x+1");
/// ```
impl From<Polynomial> for String {
  fn from(p: Polynomial) -> String {
    p.as_string("x")
  }
}

use std::fmt;

/// Implements Display trait with `x` symbol as a variable.
///
/// # Examples
///
/// Prints `expr: 2x+1`:
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// println!("expr: {}", Polynomial::linear(1.0, 2.0));
/// ```
impl fmt::Display for Polynomial {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.write_str(self.as_string("x").as_str())
  }
}

use std::ops::*;

/// Implements index operator for accessing coefficients.
///
/// An index may be interpreted as related exponent.
///
/// # Panics
///
/// Panics when index is greater than number of coefficients.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// assert_eq!(Polynomial::new(&[1.0, 2.0, 3.0])[1], 2.0);
/// assert_eq!(Polynomial::linear(1.0, 2.0)[1], 2.0);
/// ```
impl Index<usize> for Polynomial {
  type Output = f64;

  fn index(&self, idx: usize) -> &f64 {
    &self.coefficients[idx]
  }
}

/// Implements mutable index operator for accessing and
/// modifying coefficients.
///
/// An index may be interpreted as related exponent. If index
/// is greater than current number of coefficients, new coefficients
/// are added with default value of zero (so these uninitialiazed
/// terms have no effect on value or degree of the polynomial).
///
/// # Panics
///
/// May panic when coefficients cannot be resized (as in lack of memory).
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut p = Polynomial::zero();
///
/// p[0] = 2.0;
/// assert_eq!(p[0], 2.0);
/// p[123] = 4.0;
/// assert_eq!(p[122], 0.0);
/// assert_eq!(p[123], 4.0);
/// assert_eq!(p.degree(), 123);
/// ```
impl IndexMut<usize> for Polynomial {
  fn index_mut(&mut self, idx: usize) -> &mut f64 {
    if idx >= self.coefficients.len() {
      self.coefficients.resize(idx + 1, 0.0);
    }

    &mut self.coefficients[idx]
  }
}

/// Performs polynomial addition in-place.
///
/// This addition operator requires first operand to be a mutable
/// reference (which is returned back), the other operand is
/// immutable. No other new instance of Polynomial is created
/// when this operation is executed.
///
/// Polynomial addition is a linear time operation, it is
/// a simple vector addition, as one needs to add coefficients
/// of appropriate terms.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = &mut Polynomial::constant(1.0);
/// let b = &Polynomial::linear(1.0, 1.0);
///
/// let c = a + b;
///
/// assert_eq!(*c, Polynomial::linear(2.0, 1.0));
/// ```
impl<'a, 'b> Add<&'b Polynomial> for &'a mut Polynomial {
  type Output = &'a Polynomial;

  fn add(self, other: &'b Polynomial) -> &'a Polynomial {
    if other.coefficients.len() > self.coefficients.len() {
      self.coefficients.resize(other.coefficients.len(), 0.0);
    }

    for (idx, &coefficient) in other.coefficients.iter().enumerate() {
      self.coefficients[idx] += coefficient;
    }

    self
  }
}

/// Implementation of assign with addition `+=` operator.
///
/// Internally it just uses addition operator on mutable reference.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut a = Polynomial::constant(1.0);
/// let b = Polynomial::linear(1.0, 1.0);
///
/// a += b;
///
/// assert_eq!(a, Polynomial::linear(2.0, 1.0));
/// ```
impl AddAssign for Polynomial {
  fn add_assign(&mut self, other: Polynomial) {
    self + &other;
  }
}

/// Implementation of addition operator for polynomials. A new
/// instance of Polynomial is created.
///
/// Internally first operand is cloned, than assign with addition
/// is used and the modified operand is returned as a result.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = Polynomial::constant(1.0);
/// let b = Polynomial::linear(1.0, 1.0);
///
/// assert_eq!(a+b, Polynomial::linear(2.0, 1.0));
/// ```
impl Add for Polynomial {
  type Output = Polynomial;

  fn add(self, other: Polynomial) -> Polynomial {
    let mut c = self.clone();
    c += other;
    c
  }
}

/// Performs polynomial subtraction in-place.
///
/// This subtraction operator requires first operand to be a mutable
/// reference (which is returned back), the other operand is
/// immutable. No other new instance of Polynomial is created
/// when this operation is executed.
///
/// Polynomial subtraction is a linear time operation, it is
/// a simple vector addition, as one needs to subtract coefficients
/// of appropriate terms.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = &mut Polynomial::constant(1.0);
/// let b = &Polynomial::linear(1.0, 1.0);
///
/// let c = a - b;
///
/// assert_eq!(*c, Polynomial::linear(0.0, -1.0));
/// ```
impl<'a, 'b> Sub<&'b Polynomial> for &'a mut Polynomial {
  type Output = &'a Polynomial;

  fn sub(self, other: &'b Polynomial) -> &'a Polynomial {
    if other.coefficients.len() > self.coefficients.len() {
      self.coefficients.resize(other.coefficients.len(), 0.0);
    }

    for (idx, &coefficient) in other.coefficients.iter().enumerate() {
      self.coefficients[idx] -= coefficient;
    }

    self
  }
}

/// Implementation of assign with subtraction `-=` operator.
///
/// Internally it just uses subtraction operator on mutable reference.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut a = Polynomial::constant(1.0);
/// let b = Polynomial::linear(1.0, 1.0);
///
/// a -= b;
///
/// assert_eq!(a, Polynomial::linear(0.0, -1.0));
/// ```
impl SubAssign for Polynomial {
  fn sub_assign(&mut self, other: Polynomial) {
    self - &other;
  }
}

/// Implementation of subtraction operator for polynomials. A new
/// instance of Polynomial is created.
///
/// Internally first operand is cloned, than assign with subtraction
/// is used and the modified operand is returned as a result.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = Polynomial::constant(1.0);
/// let b = Polynomial::linear(1.0, 1.0);
///
/// assert_eq!(a-b, Polynomial::linear(0.0, -1.0));
/// ```
impl Sub for Polynomial {
  type Output = Polynomial;

  fn sub(self, other: Polynomial) -> Polynomial {
    let mut c = self.clone();
    c -= other;
    c
  }
}

/// Performs polynomial multiplication without creating new
/// Polynomial.
///
/// This multiplication operator requires first operand to be
/// a mutable reference (which is returned back), the other
/// operand is immutable. No other new instance of Polynomial
/// is created when this operation is executed.
///
/// Polynomial multiplication is implemented as O(n*m) operation,
/// which results in polynomial of degree n+m. Internally an
/// appropriatly sized temporary vector is used. If both polynomials
/// are degree zero, a simple arithmetic multiplication is used.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = &mut Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = &Polynomial::linear(1.0, 2.0);
///
/// let c = a * b;
///
/// assert_eq!(*c, Polynomial::new(&[0.0, 2.0, 5.0, 2.0]));
/// ```
impl<'a, 'b> Mul<&'b Polynomial> for &'a mut Polynomial {
  type Output = &'a Polynomial;

  fn mul(self, other: &'b Polynomial) -> &'a Polynomial {
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

    self
  }
}

/// Implementation of assign with multiplication `*=` operator.
///
/// Internally it just uses multiplication operator on mutable reference.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut a = Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = Polynomial::linear(1.0, 2.0);
///
/// a *= b;
///
/// assert_eq!(a, Polynomial::new(&[0.0, 2.0, 5.0, 2.0]));
/// ```
impl MulAssign for Polynomial {
  fn mul_assign(&mut self, other: Polynomial) {
    self * &other;
  }
}

/// Implementation of assign with multiplication `*=` operator for references.
///
/// Internally it just uses multiplication operator on mutable reference (it
/// is just a syntactic sugar around it).
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut a = &mut Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = &Polynomial::linear(1.0, 2.0);
///
/// a *= b;
///
/// assert_eq!(*a, Polynomial::new(&[0.0, 2.0, 5.0, 2.0]));
/// ```
impl<'a, 'b> MulAssign<&'b Polynomial> for &'a mut Polynomial {
  fn mul_assign(&mut self, other: &'b Polynomial) {
    self.mul(other);
  }
}

/// Implementation of multiplication operator for polynomials. A new
/// instance of Polynomial is created.
///
/// Internally first operand is cloned, than assign with multiplication
/// is used and the modified operand is returned as a result.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = Polynomial::linear(1.0, 2.0);
///
/// assert_eq!(a*b, Polynomial::new(&[0.0, 2.0, 5.0, 2.0]));
/// ```
impl Mul for Polynomial {
  type Output = Polynomial;

  fn mul(self, other: Polynomial) -> Polynomial {
    let mut c = self.clone();
    c *= other;
    c
  }
}

/// Specialization of assign with multiplication `*=` operator for polynomial
/// and double number.
///
/// Internally it just multiplies each of coefficient by given double number.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut a = Polynomial::new(&[0.0, 2.0, 1.0]);
///
/// a *= 2.0f64;
///
/// assert_eq!(a, Polynomial::new(&[0.0, 4.0, 2.0]));
/// ```
impl MulAssign<f64> for Polynomial {
  fn mul_assign(&mut self, other: f64) {
    let self_degree = self.degree();

    for idx in 0..self_degree+1 {
      self.coefficients[idx] *= other;
    }
  }
}

/// Performs polynomial division without creating new
/// Polynomial.
///
/// This division operator requires first operand to be
/// a mutable reference (which is returned back), the other
/// operand is immutable. No other new instance of Polynomial
/// is created when this operation is executed.
///
/// Polynomial division is implemented using long division algorithm,
/// Internally two temporary polynomials are used. However, if divisior
/// is a constant, a simple arithmetic division over each coefficient
/// of divident is used.
///
/// # Errors
///
/// This division operator does not panic on division by zero, as such
/// operation is defined on double numbers. However in special cases
/// some errors may be returned.
///
/// However division by zero of non-constant polynomial will result in
/// DivisionByZero error, as such operation is not defined.
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::polynomial::PolynomialError;
/// let a = &mut Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = &Polynomial::zero();
///
/// let c = a / b;
///
/// assert_eq!(c.unwrap_err(), PolynomialError::DivisionByZero);
/// ```
///
/// A DividentDegreeMismatch error is returned when divident degree is
/// smaller than divisor degree, as performing such operation would
/// result in nonpolynomial result.
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// # use xxcalc::polynomial::PolynomialError;
/// let a = &mut Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = &Polynomial::new(&[1.0, 2.0, 2.0, 2.0]);
///
/// let c = a / b;
///
/// assert_eq!(c.unwrap_err(), PolynomialError::DividentDegreeMismatch);
/// ```
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = &mut Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = &Polynomial::linear(1.0, 2.0);
///
/// let c = a / b;
///
/// assert_eq!(c, Ok(&Polynomial::new(&[0.75, 0.5])));
/// ```
impl<'a, 'b> Div<&'b Polynomial> for &'a mut Polynomial {
  type Output = Result<&'a Polynomial, PolynomialError>;

  fn div(self, other: &'b Polynomial) -> Result<&'a Polynomial, PolynomialError> {
    let mut self_degree = self.degree();
    let other_degree = other.degree();

    if self_degree < other_degree {
      return Err(PolynomialError::DividentDegreeMismatch);
    } else
    if other_degree == 0 {
      if other.coefficients[0] == 0.0 && self_degree > 0 {
        return Err(PolynomialError::DivisionByZero);
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

    Ok(self)
  }
}

/// Implementation of assign with division `/=` operator.
///
/// Internally it just uses division operator on mutable reference.
///
/// # Panics
///
/// It will panic when divident degree is smaller than divisor degree,
/// or if divident is a non constant polynomial and divisor is zero.
/// Internally result of division in unwrap, which may cause these errors.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let mut a = Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = Polynomial::linear(1.0, 2.0);
///
/// a /= b;
///
/// assert_eq!(a, Polynomial::new(&[0.75, 0.5]));
/// ```
impl DivAssign for Polynomial {
  fn div_assign(&mut self, other: Polynomial) {
    let _ = (self / &other).unwrap();
  }
}

/// Implementation of division operator for polynomials. A new
/// instance of Polynomial is created.
///
/// Internally first operand is cloned, than assign with division
/// is used and the modified operand is returned as a result.
///
/// # Panics
///
/// It will panic when divident degree is smaller than divisor degree,
/// or if divident is a non constant polynomial and divisor is zero.
/// Internally result of division in unwrap, which may cause these errors.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// let a = Polynomial::new(&[0.0, 2.0, 1.0]);
/// let b = Polynomial::linear(1.0, 2.0);
///
/// assert_eq!(a/b, Polynomial::new(&[0.75, 0.5]));
/// ```
impl Div for Polynomial {
  type Output = Polynomial;

  fn div(self, other: Polynomial) -> Polynomial {
    let mut c = self.clone();
    c /= other;
    c
  }
}

use std::cmp::{PartialEq, Eq};

/// Checks if two polynomials are equal.
///
/// Polynomials must have the same degree and the same
/// coefficients to be considered equal.
///
/// # Examples
///
/// ```
/// # use xxcalc::polynomial::Polynomial;
/// assert!(Polynomial::new(&[1.0, 2.0]) == Polynomial::new(&[1.0, 2.0]));
/// assert!(Polynomial::new(&[1.0, 2.0]) == Polynomial::new(&[1.0, 2.0, 0.0, 0.0]));
/// ```
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

/// Error resulting from operations on polynomials
#[derive(Debug, PartialEq)]
pub enum PolynomialError {
  /// Tried to convert non-constant polynomial to float
  NonConstantError,
  /// Divided non-constant polynomial by zero
  DivisionByZero,
  /// Divident is of smaller degree than divisor
  DividentDegreeMismatch
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
    assert_eq!(Polynomial::linear(0.0, 1.0).as_string("x"), "x");
    assert_eq!(Polynomial::linear(0.0, 2.0).as_string("x"), "2x");
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
