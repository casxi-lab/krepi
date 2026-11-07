//! Code shapes that the krepi proof gate qualifies the pinned Charon and
//! Aeneas with, one module per shape.
//!
//! `cargo xtask formal run` extracts each module separately with the pinned
//! tools and compares the outcome with `verification/qualification/cases.json`.
//! Nothing here is used by krepi: the modules record which shapes the tools
//! translate, which they reject, and which reach standard-library functions
//! that need reviewed external declarations. The shapes up to
//! `division_walk` come from the CAS project, and "the library" in their
//! documentation is the library of that project; the modules after it record
//! shapes of the provable Rust subset (`docs/conventions/provable-subset.md`).

/// The exact standard-library conversion, replaced by its reviewed external
/// declaration. The borrowed argument is always a valid Rust string.
pub mod str_from {
    pub fn copy(value: &str) -> String {
        String::from(value)
    }
}

/// Prime-field arithmetic on machine words with 64-bit intermediates.
pub mod arithmetic {
    pub fn mul_mod(a: u32, b: u32, p: u32) -> u32 {
        ((u64::from(a) * u64::from(b)) % u64::from(p)) as u32
    }

    pub fn sub_mod(a: u32, b: u32, p: u32) -> u32 {
        ((u64::from(a) + u64::from(p) - u64::from(b)) % u64::from(p)) as u32
    }

    /// Square-and-multiply with shifts and masks.
    pub fn pow_mod(base: u32, exponent: u32, p: u32) -> u32 {
        let mut base = base % p;
        let mut exponent = exponent;
        let mut result = 1 % p;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = mul_mod(result, base, p);
            }
            exponent >>= 1;
            base = mul_mod(base, base, p);
        }
        result
    }
}

/// Lossless integer conversions as the numerical code writes them: the
/// exponent `-bits - 4` of a threshold formed with an `as` cast and with
/// `i64::from`, and a `u32` widened with `u64::from`; the magnitude of an
/// `i64` as a `u64` formed with `as` casts in arithmetic that cannot
/// overflow, a `u64` converted into `usize` with an `as` cast after a bound
/// check against `usize::MAX as u64`, and a `checked_sub` of an `i64` whose
/// result a `match` takes apart, returning early when it is `None`.
pub mod integer_conversions {
    pub fn exponent_by_cast(bits: u32) -> i64 {
        -(bits as i64) - 4
    }

    pub fn exponent_by_from(bits: u32) -> i64 {
        -i64::from(bits) - 4
    }

    pub fn widened(bits: u32) -> u64 {
        u64::from(bits)
    }

    pub fn magnitude(value: i64) -> u64 {
        if value >= 0 {
            value as u64
        } else {
            (-(value + 1)) as u64 + 1
        }
    }

    pub struct Overflow;

    pub fn shift_within(shift: u64) -> Result<usize, Overflow> {
        if shift > usize::MAX as u64 {
            return Err(Overflow);
        }
        Ok(shift as usize)
    }

    pub fn exponent_below(guess: i64, bits: u32) -> Result<u64, Overflow> {
        let exponent = match guess.checked_sub(bits as i64 - 1) {
            Some(exponent) => exponent,
            None => return Err(Overflow),
        };
        Ok(magnitude(exponent))
    }
}

/// Checked and saturating machine arithmetic written with `match`.
pub mod checked {
    pub fn add_within(work: u64, amount: u64, max: u64) -> Option<u64> {
        match work.checked_add(amount) {
            Some(total) if total <= max => Some(total),
            _ => None,
        }
    }

    pub fn saturating_total(a: usize, b: usize) -> usize {
        a.saturating_add(b)
    }
}

/// The same budget check written with `Option` combinators and a closure.
pub mod option_combinators {
    pub fn add_within(work: u64, amount: u64, max: u64) -> Option<u64> {
        work.checked_add(amount).filter(|&total| total <= max)
    }
}

/// A fallible charge shared by the loop shapes.
pub mod budget {
    pub struct Budget {
        pub left: u64,
    }

    pub struct Exhausted;

    impl Budget {
        pub fn take(&mut self, amount: u64) -> Result<(), Exhausted> {
            if amount > self.left {
                return Err(Exhausted);
            }
            self.left -= amount;
            Ok(())
        }
    }
}

/// `?` inside a single loop.
pub mod single_loop {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_each(budget: &mut Budget, count: u32) -> Result<u32, Exhausted> {
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            done += 1;
        }
        Ok(done)
    }
}

/// `?` inside the inner loop of two nested loops.
pub mod nested_loop {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_grid(budget: &mut Budget, rows: u32, columns: u32) -> Result<u64, Exhausted> {
        let mut cells = 0u64;
        let mut row = 0;
        while row < rows {
            let mut column = 0;
            while column < columns {
                budget.take(1)?;
                cells += 1;
                column += 1;
            }
            row += 1;
        }
        Ok(cells)
    }
}

/// The nested loop with its inner loop moved into a helper function.
pub mod split_loop {
    use crate::budget::{Budget, Exhausted};

    fn charge_row(budget: &mut Budget, columns: u32) -> Result<u64, Exhausted> {
        let mut cells = 0u64;
        let mut column = 0;
        while column < columns {
            budget.take(1)?;
            cells += 1;
            column += 1;
        }
        Ok(cells)
    }

    pub fn charge_grid(budget: &mut Budget, rows: u32, columns: u32) -> Result<u64, Exhausted> {
        let mut cells = 0u64;
        let mut row = 0;
        while row < rows {
            cells += charge_row(budget, columns)?;
            row += 1;
        }
        Ok(cells)
    }
}

/// `break` and `?` in one loop, followed by a return.
pub mod loop_break_tail {
    use crate::budget::{Budget, Exhausted};

    pub fn first_zero(budget: &mut Budget, values: &[u32]) -> Result<usize, Exhausted> {
        let mut index = 0;
        while index < values.len() {
            budget.take(1)?;
            if values[index] == 0 {
                break;
            }
            index += 1;
        }
        Ok(index)
    }
}

/// `break` and `?` in a loop inside a branch, with code after the branch.
pub mod loop_break_branch {
    use crate::budget::{Budget, Exhausted};

    pub fn first_zero_or_end(
        budget: &mut Budget,
        values: &[u32],
        search: bool,
    ) -> Result<usize, Exhausted> {
        let mut index = 0;
        if search {
            while index < values.len() {
                budget.take(1)?;
                if values[index] == 0 {
                    break;
                }
                index += 1;
            }
        } else {
            index = values.len();
        }
        budget.take(1)?;
        Ok(index)
    }
}

/// Iterator adapters and `collect`.
pub mod iterator_adapters {
    pub fn incremented(values: &[u32]) -> Vec<u32> {
        values.iter().map(|value| value.wrapping_add(1)).collect()
    }
}

/// The same computation with an index loop.
pub mod index_loop {
    pub fn incremented(values: &[u32]) -> Vec<u32> {
        let mut out = Vec::with_capacity(values.len());
        let mut index = 0;
        while index < values.len() {
            out.push(values[index].wrapping_add(1));
            index += 1;
        }
        out
    }
}

/// Comparison of `Option<&T>` values.
pub mod option_reference_eq {
    pub fn trim(values: &mut Vec<u32>) {
        while values.last() == Some(&0) {
            values.pop();
        }
    }
}

/// Trimming trailing zeros by index.
pub mod trim_by_index {
    pub fn trim(values: &mut Vec<u32>) {
        while !values.is_empty() && values[values.len() - 1] == 0 {
            values.pop();
        }
    }
}

/// Vector operations used by coefficient vectors.
pub mod vector_operations {
    pub fn edit(values: &mut Vec<u64>, extra: u64) -> usize {
        values.push(extra);
        let last = values.pop().unwrap_or(0);
        values.truncate(4);
        if values.len() >= 2 {
            values.swap(0, 1);
        }
        if let Some(first) = values.first_mut() {
            *first = first.wrapping_add(last);
        }
        values.len()
    }
}

/// A method taking an `FnOnce` closure over `&mut Self`.
pub mod closure_parameter {
    pub struct Depth {
        pub current: usize,
        pub limit: usize,
    }

    pub struct TooDeep;

    impl Depth {
        pub fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> Result<T, TooDeep> {
            if self.current >= self.limit {
                return Err(TooDeep);
            }
            self.current += 1;
            let result = f(self);
            self.current -= 1;
            Ok(result)
        }
    }

    pub fn inner_depth(depth: &mut Depth) -> Result<usize, TooDeep> {
        depth.nested(|inner| inner.current)
    }
}

/// A generic algorithm over a trait, with one implementation.
pub mod generic_trait {
    pub trait Ring: Sized {
        fn zero() -> Self;
        fn add(&self, other: &Self) -> Self;
    }

    #[derive(Clone, Copy)]
    pub struct Mod7(pub u8);

    impl Ring for Mod7 {
        fn zero() -> Self {
            Mod7(0)
        }

        fn add(&self, other: &Self) -> Self {
            Mod7((self.0 % 7 + other.0 % 7) % 7)
        }
    }

    pub fn sum<R: Ring>(values: &[R]) -> R {
        let mut total = R::zero();
        let mut index = 0;
        while index < values.len() {
            total = total.add(&values[index]);
            index += 1;
        }
        total
    }

    pub fn sum_mod7(values: &[Mod7]) -> Mod7 {
        sum(values)
    }
}

/// An ordered map keyed by integers.
pub mod ordered_maps {
    use std::collections::BTreeMap;

    pub fn bump(map: &mut BTreeMap<u32, u64>, key: u32) -> u64 {
        let value = map.get(&key).copied().unwrap_or(0).saturating_add(1);
        map.insert(key, value);
        value
    }
}

/// Shared immutable values and pointer identity.
pub mod shared_pointers {
    use std::sync::Arc;

    pub fn same(a: &Arc<Vec<u32>>, b: &Arc<Vec<u32>>) -> bool {
        Arc::ptr_eq(a, b) || **a == **b
    }
}

/// A recursive expression type.
pub mod recursion {
    pub enum Expr {
        Number(u32),
        Add(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
    }

    pub fn eval(expr: &Expr) -> u64 {
        match expr {
            Expr::Number(value) => u64::from(*value),
            Expr::Add(a, b) => eval(a).wrapping_add(eval(b)),
            Expr::Mul(a, b) => eval(a).wrapping_mul(eval(b)),
        }
    }
}

/// Message formatting as used by errors.
pub mod formatting {
    pub fn message(resource: &str) -> String {
        format!("resource limit exceeded: {resource}")
    }
}

/// binary64 arithmetic in an error-free transformation.
pub mod floats {
    pub fn two_sum(a: f64, b: f64) -> (f64, f64) {
        let sum = a + b;
        let b_virtual = sum - a;
        let error = (a - (sum - b_virtual)) + (b - b_virtual);
        (sum, error)
    }
}

/// binary64 data stored as bit patterns, with every floating-point operation
/// in one primitive module that extraction cuts. The rest is integer code on
/// the bits and calls of the primitives: classification, negation and the
/// neighbours of a datum, the error-free sum and product, directed roundings
/// formed from the rounding to nearest and the sign bit of its error, the
/// endpoints of an interval sum, and a dot product in increasing index order.
pub mod binary64_bits {
    /// A binary64 datum as its IEEE 754 bit pattern.
    #[derive(Clone, Copy)]
    pub struct Binary64 {
        bits: u64,
    }

    /// A closed interval with binary64 endpoints.
    #[derive(Clone, Copy)]
    pub struct Interval {
        lo: Binary64,
        hi: Binary64,
    }

    const SIGN: u64 = 0x8000_0000_0000_0000;
    const MAGNITUDE: u64 = 0x7fff_ffff_ffff_ffff;
    const INFINITY: u64 = 0x7ff0_0000_0000_0000;
    const MAX_FINITE: u64 = 0x7fef_ffff_ffff_ffff;

    /// The only functions that use floating point; extraction cuts them, so
    /// their signatures mention no floating-point type.
    pub mod primitive {
        use super::Binary64;

        pub fn add(a: Binary64, b: Binary64) -> Binary64 {
            Binary64 {
                bits: (f64::from_bits(a.bits) + f64::from_bits(b.bits)).to_bits(),
            }
        }

        pub fn sub(a: Binary64, b: Binary64) -> Binary64 {
            Binary64 {
                bits: (f64::from_bits(a.bits) - f64::from_bits(b.bits)).to_bits(),
            }
        }

        pub fn mul(a: Binary64, b: Binary64) -> Binary64 {
            Binary64 {
                bits: (f64::from_bits(a.bits) * f64::from_bits(b.bits)).to_bits(),
            }
        }

        pub fn fma(a: Binary64, b: Binary64, c: Binary64) -> Binary64 {
            Binary64 {
                bits: f64::from_bits(a.bits)
                    .mul_add(f64::from_bits(b.bits), f64::from_bits(c.bits))
                    .to_bits(),
            }
        }
    }

    pub fn negate(a: Binary64) -> Binary64 {
        Binary64 {
            bits: a.bits ^ SIGN,
        }
    }

    pub fn sign_bit(a: Binary64) -> bool {
        a.bits & SIGN != 0
    }

    pub fn is_finite(a: Binary64) -> bool {
        a.bits & MAGNITUDE < INFINITY
    }

    pub fn is_nan(a: Binary64) -> bool {
        a.bits & MAGNITUDE > INFINITY
    }

    pub fn is_zero(a: Binary64) -> bool {
        a.bits & MAGNITUDE == 0
    }

    /// The least datum above `a`; NaN and positive infinity are unchanged.
    pub fn next_up(a: Binary64) -> Binary64 {
        if is_nan(a) || a.bits == INFINITY {
            return a;
        }
        if is_zero(a) {
            return Binary64 { bits: 1 };
        }
        if sign_bit(a) {
            Binary64 { bits: a.bits - 1 }
        } else {
            Binary64 { bits: a.bits + 1 }
        }
    }

    /// The greatest datum below `a`; NaN and negative infinity are unchanged.
    pub fn next_down(a: Binary64) -> Binary64 {
        negate(next_up(negate(a)))
    }

    /// The six operations of the error-free sum.
    pub fn two_sum(a: Binary64, b: Binary64) -> (Binary64, Binary64) {
        let sum = primitive::add(a, b);
        let b_virtual = primitive::sub(sum, a);
        let a_virtual = primitive::sub(sum, b_virtual);
        let error = primitive::add(primitive::sub(a, a_virtual), primitive::sub(b, b_virtual));
        (sum, error)
    }

    /// The error-free product with a fused multiply-add.
    pub fn two_product(a: Binary64, b: Binary64) -> (Binary64, Binary64) {
        let product = primitive::mul(a, b);
        (product, primitive::fma(a, b, negate(product)))
    }

    /// The rounding of `a + b` toward negative infinity for operands that are
    /// not NaN: the rounding to nearest, one step lower when its error is
    /// negative or not finite.
    pub fn add_down(a: Binary64, b: Binary64) -> Binary64 {
        let (sum, error) = two_sum(a, b);
        if is_finite(sum) {
            if is_finite(error) && !sign_bit(error) {
                sum
            } else {
                next_down(sum)
            }
        } else if is_finite(a) && is_finite(b) && !sign_bit(sum) {
            Binary64 { bits: MAX_FINITE }
        } else {
            sum
        }
    }

    /// The rounding of `a + b` toward positive infinity, by symmetry.
    pub fn add_up(a: Binary64, b: Binary64) -> Binary64 {
        negate(add_down(negate(a), negate(b)))
    }

    /// The rounding of `a * b` toward positive infinity for finite operands:
    /// the rounding to nearest, one step higher when the sign bit of the
    /// residual `p - a b` is set, which a correctly rounded residual keeps
    /// even when it rounds to zero.
    pub fn mul_up(a: Binary64, b: Binary64) -> Binary64 {
        let product = primitive::mul(a, b);
        if !is_finite(product) {
            return if sign_bit(product) {
                Binary64 {
                    bits: SIGN | MAX_FINITE,
                }
            } else {
                product
            };
        }
        let residual = primitive::fma(negate(a), b, product);
        if sign_bit(residual) {
            next_up(product)
        } else {
            product
        }
    }

    /// The outward-rounded sum of two intervals.
    pub fn interval_add(x: Interval, y: Interval) -> Interval {
        Interval {
            lo: add_down(x.lo, y.lo),
            hi: add_up(x.hi, y.hi),
        }
    }

    /// A dot product in increasing index order over the common length.
    pub fn dot(x: &[Binary64], y: &[Binary64]) -> Binary64 {
        let mut total = Binary64 { bits: 0 };
        let mut index = 0;
        while index < x.len() && index < y.len() {
            total = primitive::add(total, primitive::mul(x[index], y[index]));
            index += 1;
        }
        total
    }
}

/// The error-free sum of `floats` with its arithmetic moved into a cut
/// primitive module, so that `f64` values cross the signatures of the
/// translated code, and a finiteness check on the bits of an `f64` argument.
pub mod binary64_values {
    pub mod primitive {
        pub fn add(a: f64, b: f64) -> f64 {
            a + b
        }

        pub fn sub(a: f64, b: f64) -> f64 {
            a - b
        }
    }

    pub fn two_sum(a: f64, b: f64) -> (f64, f64) {
        let sum = primitive::add(a, b);
        let b_virtual = primitive::sub(sum, a);
        let a_virtual = primitive::sub(sum, b_virtual);
        let error = primitive::add(primitive::sub(a, a_virtual), primitive::sub(b, b_virtual));
        (sum, error)
    }

    pub fn finite_bits(value: f64) -> Option<u64> {
        let bits = value.to_bits();
        if bits & 0x7fff_ffff_ffff_ffff < 0x7ff0_0000_0000_0000 {
            Some(bits)
        } else {
            None
        }
    }
}

/// Two reads of the monotonic clock in one call.
pub mod clock {
    use std::time::Instant;

    pub fn expired_twice(deadline: Instant) -> (bool, bool) {
        let first = Instant::now() >= deadline;
        let second = Instant::now() >= deadline;
        (first, second)
    }
}

/// A relaxed atomic load, as used by cancellation.
pub mod atomics {
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    };

    pub fn cancelled(flag: &Arc<AtomicBool>) -> bool {
        flag.load(Ordering::Relaxed)
    }
}

/// External observations reached through `&mut self`. Extraction keeps the
/// observer type and its method opaque, so a model can supply a different
/// value at every call.
pub mod observations {
    pub struct Probe {
        reads: u64,
    }

    impl Probe {
        pub fn new() -> Self {
            Self { reads: 0 }
        }

        pub fn observe(&mut self) -> bool {
            self.reads = self.reads.wrapping_add(1);
            self.reads.is_multiple_of(2)
        }
    }

    impl Default for Probe {
        fn default() -> Self {
            Self::new()
        }
    }

    pub fn observe_twice(probe: &mut Probe) -> (bool, bool) {
        let first = probe.observe();
        let second = probe.observe();
        (first, second)
    }
}

/// A sum over a slice with an index loop.
pub mod slices {
    pub fn total(values: &[u32]) -> u64 {
        let mut total = 0u64;
        let mut index = 0;
        while index < values.len() {
            total += u64::from(values[index]);
            index += 1;
        }
        total
    }
}

/// A stand-in for the request context of the field interface below: a work
/// budget whose charge fails once it is exhausted, and the failures that the
/// interface reports.
pub mod meter {
    #[derive(Clone, Copy)]
    pub enum Failure {
        Exhausted,
        DivisionByZero,
    }

    pub struct Meter {
        pub left: u64,
    }

    impl Meter {
        pub fn charge(&mut self, amount: u64) -> Result<(), Failure> {
            if amount > self.left {
                return Err(Failure::Exhausted);
            }
            self.left -= amount;
            Ok(())
        }
    }
}

/// A crate-private field interface with an associated element type: methods
/// take `&self`, element references and the meter, and return `Result`.
/// Generic algorithms with one loop and `?`, and two implementations: a prime
/// field whose implementation, in a child module, delegates to its private
/// inherent arithmetic, and a borrowed view with a lifetime parameter.
pub mod field_interface {
    use crate::meter::{Failure, Meter};

    /// The three answers of a zero test.
    #[derive(Clone, Copy)]
    pub enum ZeroTest {
        Zero,
        Nonzero,
        Unknown,
    }

    pub(crate) trait FieldOps {
        type Element: Clone;

        fn zero(&self) -> Self::Element;
        fn zero_test(&self, a: &Self::Element) -> ZeroTest;
        fn add(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            meter: &mut Meter,
        ) -> Result<Self::Element, Failure>;
        fn mul(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            meter: &mut Meter,
        ) -> Result<Self::Element, Failure>;
        fn inverse(&self, a: &Self::Element, meter: &mut Meter) -> Result<Self::Element, Failure>;
    }

    /// Horner evaluation: one loop with `?`.
    pub(crate) fn evaluate<F: FieldOps>(
        field: &F,
        coefficients: &[F::Element],
        point: &F::Element,
        meter: &mut Meter,
    ) -> Result<F::Element, Failure> {
        let mut value = field.zero();
        let mut index = coefficients.len();
        while index > 0 {
            index -= 1;
            let product = field.mul(&value, point, meter)?;
            value = field.add(&product, &coefficients[index], meter)?;
        }
        Ok(value)
    }

    /// The inverse of the highest coefficient whose zero test answers
    /// `Nonzero`: a loop with `?` and `break`, the coefficient cloned out of
    /// the slice, and a three-valued `match`.
    pub(crate) fn leading_inverse<F: FieldOps>(
        field: &F,
        coefficients: &[F::Element],
        meter: &mut Meter,
    ) -> Result<Option<F::Element>, Failure> {
        let mut index = coefficients.len();
        let mut leading = None;
        while index > 0 {
            index -= 1;
            meter.charge(1)?;
            match field.zero_test(&coefficients[index]) {
                ZeroTest::Nonzero => {
                    leading = Some(coefficients[index].clone());
                    break;
                }
                ZeroTest::Zero | ZeroTest::Unknown => {}
            }
        }
        match leading {
            Some(value) => Ok(Some(field.inverse(&value, meter)?)),
            None => Ok(None),
        }
    }

    /// A prime field whose arithmetic is proved on its inherent methods.
    #[derive(Clone, Copy)]
    pub struct PrimeField {
        pub p: u32,
    }

    impl PrimeField {
        fn add(self, a: u32, b: u32) -> u32 {
            ((u64::from(a) + u64::from(b)) % u64::from(self.p)) as u32
        }

        fn mul(self, a: u32, b: u32) -> u32 {
            ((u64::from(a) * u64::from(b)) % u64::from(self.p)) as u32
        }

        fn inverse(self, a: u32, meter: &mut Meter) -> Result<u32, Failure> {
            if a == 0 {
                return Err(Failure::DivisionByZero);
            }
            let mut a = a;
            let mut n = self.p - 2;
            let mut result = 1;
            while n != 0 {
                meter.charge(1)?;
                if n & 1 != 0 {
                    result = self.mul(result, a);
                }
                n >>= 1;
                if n != 0 {
                    a = self.mul(a, a);
                }
            }
            Ok(result)
        }
    }

    /// The implementation lives in a child module, which sees the private
    /// inherent methods and calls them instead of copying them.
    mod prime {
        use super::{FieldOps, PrimeField, ZeroTest};
        use crate::meter::{Failure, Meter};

        impl FieldOps for PrimeField {
            type Element = u32;

            fn zero(&self) -> u32 {
                0
            }

            fn zero_test(&self, a: &u32) -> ZeroTest {
                if *a == 0 {
                    ZeroTest::Zero
                } else {
                    ZeroTest::Nonzero
                }
            }

            fn add(&self, a: &u32, b: &u32, meter: &mut Meter) -> Result<u32, Failure> {
                meter.charge(1)?;
                Ok(PrimeField::add(*self, *a, *b))
            }

            fn mul(&self, a: &u32, b: &u32, meter: &mut Meter) -> Result<u32, Failure> {
                meter.charge(1)?;
                Ok(PrimeField::mul(*self, *a, *b))
            }

            fn inverse(&self, a: &u32, meter: &mut Meter) -> Result<u32, Failure> {
                PrimeField::inverse(*self, *a, meter)
            }
        }
    }

    /// A borrowed view of a parent together with the polynomial variable:
    /// the two-element field with `bool` elements.
    pub struct Binary<'a> {
        pub variable: &'a str,
    }

    impl FieldOps for Binary<'_> {
        type Element = bool;

        fn zero(&self) -> bool {
            false
        }

        fn zero_test(&self, a: &bool) -> ZeroTest {
            if *a {
                ZeroTest::Nonzero
            } else {
                ZeroTest::Zero
            }
        }

        fn add(&self, a: &bool, b: &bool, meter: &mut Meter) -> Result<bool, Failure> {
            meter.charge(1)?;
            Ok(*a != *b)
        }

        fn mul(&self, a: &bool, b: &bool, meter: &mut Meter) -> Result<bool, Failure> {
            meter.charge(1)?;
            Ok(*a && *b)
        }

        fn inverse(&self, a: &bool, meter: &mut Meter) -> Result<bool, Failure> {
            meter.charge(1)?;
            if *a {
                Ok(true)
            } else {
                Err(Failure::DivisionByZero)
            }
        }
    }

    pub fn evaluate_prime(
        field: &PrimeField,
        coefficients: &[u32],
        point: u32,
        meter: &mut Meter,
    ) -> Result<u32, Failure> {
        evaluate(field, coefficients, &point, meter)
    }

    pub fn evaluate_binary(
        field: &Binary<'_>,
        coefficients: &[bool],
        point: bool,
        meter: &mut Meter,
    ) -> Result<bool, Failure> {
        evaluate(field, coefficients, &point, meter)
    }

    pub fn leading_inverse_prime(
        field: &PrimeField,
        coefficients: &[u32],
        meter: &mut Meter,
    ) -> Result<Option<u32>, Failure> {
        leading_inverse(field, coefficients, meter)
    }
}

/// A polynomial interface as a subtrait of an element interface, each with
/// its own associated type, and a generic algorithm that calls the methods of
/// both. The module uses the budget of the loop shapes, so its generated code
/// shares no enumeration with the field interface.
pub mod polynomial_interface {
    use crate::budget::{Budget, Exhausted};

    pub(crate) trait Coefficients {
        type Element: Clone;

        fn of_integer(&self, n: u32, budget: &mut Budget) -> Result<Self::Element, Exhausted>;
        fn mul(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted>;
    }

    pub(crate) trait PolynomialOps: Coefficients {
        type Poly;

        fn empty(&self) -> Self::Poly;
        /// None for the zero polynomial.
        fn degree(&self, p: &Self::Poly) -> Option<usize>;
        /// The coefficient of `x^degree`, returned by value.
        fn coefficient(&self, p: &Self::Poly, degree: usize) -> Self::Element;
        fn set_coefficient(
            &self,
            p: &mut Self::Poly,
            degree: usize,
            value: Self::Element,
            budget: &mut Budget,
        ) -> Result<(), Exhausted>;
    }

    /// The formal derivative; integers enter through `n * 1`. The zero
    /// polynomial sets the loop bound instead of returning early.
    pub(crate) fn derivative<R: PolynomialOps>(
        ring: &R,
        p: &R::Poly,
        budget: &mut Budget,
    ) -> Result<R::Poly, Exhausted> {
        let mut result = ring.empty();
        let end = match ring.degree(p) {
            Some(top) => top + 1,
            None => 1,
        };
        let mut degree = 1;
        while degree < end {
            let n = ring.of_integer(degree as u32, budget)?;
            let c = ring.coefficient(p, degree);
            let term = ring.mul(&c, &n, budget)?;
            ring.set_coefficient(&mut result, degree - 1, term, budget)?;
            degree += 1;
        }
        Ok(result)
    }

    /// Removes trailing zeros by index.
    fn trim(p: &mut Vec<u32>) {
        while !p.is_empty() && p[p.len() - 1] == 0 {
            p.pop();
        }
    }

    /// Integers modulo `p`.
    pub struct Modular {
        pub p: u32,
    }

    impl Coefficients for Modular {
        type Element = u32;

        fn of_integer(&self, n: u32, budget: &mut Budget) -> Result<u32, Exhausted> {
            budget.take(1)?;
            Ok(n % self.p)
        }

        fn mul(&self, a: &u32, b: &u32, budget: &mut Budget) -> Result<u32, Exhausted> {
            budget.take(1)?;
            Ok(((u64::from(*a) * u64::from(*b)) % u64::from(self.p)) as u32)
        }
    }

    /// Dense coefficient vectors.
    impl PolynomialOps for Modular {
        type Poly = Vec<u32>;

        fn empty(&self) -> Vec<u32> {
            Vec::new()
        }

        fn degree(&self, p: &Vec<u32>) -> Option<usize> {
            if p.is_empty() {
                None
            } else {
                Some(p.len() - 1)
            }
        }

        fn coefficient(&self, p: &Vec<u32>, degree: usize) -> u32 {
            if degree < p.len() { p[degree] } else { 0 }
        }

        fn set_coefficient(
            &self,
            p: &mut Vec<u32>,
            degree: usize,
            value: u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            budget.take(1)?;
            while p.len() <= degree {
                p.push(0);
            }
            p[degree] = value;
            trim(p);
            Ok(())
        }
    }

    pub fn derivative_modular(
        ring: &Modular,
        p: &Vec<u32>,
        budget: &mut Budget,
    ) -> Result<Vec<u32>, Exhausted> {
        derivative(ring, p, budget)
    }
}

/// A trait method with a default body, used by one implementation and
/// overridden by another.
pub mod default_method {
    use crate::budget::{Budget, Exhausted};

    pub(crate) trait Additive {
        type Element;

        fn add(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted>;
        fn neg(&self, a: &Self::Element, budget: &mut Budget) -> Result<Self::Element, Exhausted>;

        /// `a - b` as `a + (-b)`.
        fn sub(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted> {
            let negated = self.neg(b, budget)?;
            self.add(a, &negated, budget)
        }
    }

    /// Integers modulo `2^32`, using the default `sub`.
    pub struct Wrapping;

    impl Additive for Wrapping {
        type Element = u32;

        fn add(&self, a: &u32, b: &u32, budget: &mut Budget) -> Result<u32, Exhausted> {
            budget.take(1)?;
            Ok(a.wrapping_add(*b))
        }

        fn neg(&self, a: &u32, budget: &mut Budget) -> Result<u32, Exhausted> {
            budget.take(1)?;
            Ok(0u32.wrapping_sub(*a))
        }
    }

    /// Integers modulo `2^8`, overriding `sub`.
    pub struct Byte;

    impl Additive for Byte {
        type Element = u8;

        fn add(&self, a: &u8, b: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            Ok(a.wrapping_add(*b))
        }

        fn neg(&self, a: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            Ok(0u8.wrapping_sub(*a))
        }

        fn sub(&self, a: &u8, b: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            Ok(a.wrapping_sub(*b))
        }
    }

    pub(crate) fn difference<A: Additive>(
        ring: &A,
        a: &A::Element,
        b: &A::Element,
        budget: &mut Budget,
    ) -> Result<A::Element, Exhausted> {
        ring.sub(a, b, budget)
    }

    pub fn difference_wrapping(a: u32, b: u32, budget: &mut Budget) -> Result<u32, Exhausted> {
        difference(&Wrapping, &a, &b, budget)
    }

    pub fn difference_byte(a: u8, b: u8, budget: &mut Budget) -> Result<u8, Exhausted> {
        difference(&Byte, &a, &b, budget)
    }
}

/// A static registry of plain records: names stored as zero-padded ASCII
/// byte arrays with a length, a lookup by an index loop that compares names
/// byte by byte in a helper, access from a fieldless identifier by an
/// exhaustive `match` that returns a copy of the record, and a kernel
/// identifier dispatched by a `match`.
pub mod registry_records {
    #[derive(Clone, Copy)]
    pub enum FunctionId {
        Sin,
        Exp,
        Log,
        Rootn,
    }

    #[derive(Clone, Copy)]
    pub enum Role {
        Operand,
        Degree,
    }

    #[derive(Clone, Copy)]
    pub enum Kernel {
        Sine,
        Exponential,
        Logarithm,
        Root,
    }

    #[derive(Clone, Copy)]
    pub struct FunctionRecord {
        pub id: FunctionId,
        /// The canonical name, padded with zero bytes.
        pub name: [u8; 8],
        pub length: usize,
        pub arity: usize,
        pub roles: [Role; 2],
        pub kernel: Kernel,
    }

    pub static RECORDS: [FunctionRecord; 4] = [
        FunctionRecord {
            id: FunctionId::Sin,
            name: *b"sin\0\0\0\0\0",
            length: 3,
            arity: 1,
            roles: [Role::Operand, Role::Operand],
            kernel: Kernel::Sine,
        },
        FunctionRecord {
            id: FunctionId::Exp,
            name: *b"exp\0\0\0\0\0",
            length: 3,
            arity: 1,
            roles: [Role::Operand, Role::Operand],
            kernel: Kernel::Exponential,
        },
        FunctionRecord {
            id: FunctionId::Log,
            name: *b"log\0\0\0\0\0",
            length: 3,
            arity: 1,
            roles: [Role::Operand, Role::Operand],
            kernel: Kernel::Logarithm,
        },
        FunctionRecord {
            id: FunctionId::Rootn,
            name: *b"rootn\0\0\0",
            length: 5,
            arity: 2,
            roles: [Role::Operand, Role::Degree],
            kernel: Kernel::Root,
        },
    ];

    /// Whether the record is named `name`, compared byte by byte.
    fn named(record: &FunctionRecord, name: &[u8]) -> bool {
        if record.length != name.len() {
            return false;
        }
        let mut index = 0;
        while index < record.length {
            if record.name[index] != name[index] {
                return false;
            }
            index += 1;
        }
        true
    }

    pub fn lookup(name: &[u8]) -> Option<FunctionId> {
        let mut index = 0;
        while index < RECORDS.len() {
            if named(&RECORDS[index], name) {
                return Some(RECORDS[index].id);
            }
            index += 1;
        }
        None
    }

    pub fn record(id: FunctionId) -> FunctionRecord {
        match id {
            FunctionId::Sin => RECORDS[0],
            FunctionId::Exp => RECORDS[1],
            FunctionId::Log => RECORDS[2],
            FunctionId::Rootn => RECORDS[3],
        }
    }

    fn halve(x: u64) -> u64 {
        x / 2
    }

    fn double(x: u64) -> u64 {
        x.wrapping_mul(2)
    }

    pub fn evaluate(id: FunctionId, x: u64) -> u64 {
        match record(id).kernel {
            Kernel::Sine | Kernel::Logarithm => halve(x),
            Kernel::Exponential => double(x),
            Kernel::Root => x,
        }
    }
}

/// Access from a fieldless identifier by an exhaustive `match` to a
/// `&'static` reference into a static array of records, and a caller that
/// reads a field through the returned reference.
pub mod registry_static_reference {
    #[derive(Clone, Copy)]
    pub enum FunctionId {
        Sin,
        Rootn,
    }

    pub struct FunctionRecord {
        pub name: [u8; 8],
        pub length: usize,
        pub arity: usize,
    }

    pub static RECORDS: [FunctionRecord; 2] = [
        FunctionRecord {
            name: *b"sin\0\0\0\0\0",
            length: 3,
            arity: 1,
        },
        FunctionRecord {
            name: *b"rootn\0\0\0",
            length: 5,
            arity: 2,
        },
    ];

    pub fn record(id: FunctionId) -> &'static FunctionRecord {
        match id {
            FunctionId::Sin => &RECORDS[0],
            FunctionId::Rootn => &RECORDS[1],
        }
    }

    pub fn arity(id: FunctionId) -> usize {
        record(id).arity
    }
}

/// The registry of `registry_records` with names stored as `&'static str`
/// string constants and compared with `==`.
pub mod registry_str_names {
    #[derive(Clone, Copy)]
    pub enum FunctionId {
        Sin,
        Exp,
        Log,
        Rootn,
    }

    #[derive(Clone, Copy)]
    pub enum Role {
        Operand,
        Degree,
    }

    #[derive(Clone, Copy)]
    pub enum Kernel {
        Sine,
        Exponential,
        Logarithm,
        Root,
    }

    pub struct FunctionRecord {
        pub id: FunctionId,
        pub name: &'static str,
        pub arity: usize,
        pub roles: [Role; 2],
        pub kernel: Kernel,
    }

    pub static RECORDS: [FunctionRecord; 4] = [
        FunctionRecord {
            id: FunctionId::Sin,
            name: "sin",
            arity: 1,
            roles: [Role::Operand, Role::Operand],
            kernel: Kernel::Sine,
        },
        FunctionRecord {
            id: FunctionId::Exp,
            name: "exp",
            arity: 1,
            roles: [Role::Operand, Role::Operand],
            kernel: Kernel::Exponential,
        },
        FunctionRecord {
            id: FunctionId::Log,
            name: "log",
            arity: 1,
            roles: [Role::Operand, Role::Operand],
            kernel: Kernel::Logarithm,
        },
        FunctionRecord {
            id: FunctionId::Rootn,
            name: "rootn",
            arity: 2,
            roles: [Role::Operand, Role::Degree],
            kernel: Kernel::Root,
        },
    ];

    pub fn lookup(name: &str) -> Option<FunctionId> {
        let mut index = 0;
        while index < RECORDS.len() {
            if RECORDS[index].name == name {
                return Some(RECORDS[index].id);
            }
            index += 1;
        }
        None
    }

    pub fn record(id: FunctionId) -> &'static FunctionRecord {
        match id {
            FunctionId::Sin => &RECORDS[0],
            FunctionId::Exp => &RECORDS[1],
            FunctionId::Log => &RECORDS[2],
            FunctionId::Rootn => &RECORDS[3],
        }
    }

    fn halve(x: u64) -> u64 {
        x / 2
    }

    fn double(x: u64) -> u64 {
        x.wrapping_mul(2)
    }

    pub fn evaluate(id: FunctionId, x: u64) -> u64 {
        match record(id).kernel {
            Kernel::Sine | Kernel::Logarithm => halve(x),
            Kernel::Exponential => double(x),
            Kernel::Root => x,
        }
    }
}

/// The registry with `&'static str` names in a `const` array of `Copy`
/// records: lookup by an index loop that compares names with `==`, and access
/// from an identifier by an exhaustive `match` that returns a copy.
pub mod const_str_names {
    #[derive(Clone, Copy)]
    pub enum ConstId {
        Sin,
        Rootn,
    }

    #[derive(Clone, Copy)]
    pub struct ConstRecord {
        pub id: ConstId,
        pub name: &'static str,
        pub arity: usize,
    }

    pub const RECORDS: [ConstRecord; 2] = [
        ConstRecord {
            id: ConstId::Sin,
            name: "sin",
            arity: 1,
        },
        ConstRecord {
            id: ConstId::Rootn,
            name: "rootn",
            arity: 2,
        },
    ];

    pub fn lookup(name: &str) -> Option<ConstId> {
        let mut index = 0;
        while index < RECORDS.len() {
            if RECORDS[index].name == name {
                return Some(RECORDS[index].id);
            }
            index += 1;
        }
        None
    }

    pub fn record(id: ConstId) -> ConstRecord {
        match id {
            ConstId::Sin => RECORDS[0],
            ConstId::Rootn => RECORDS[1],
        }
    }

    pub fn arity(id: ConstId) -> usize {
        record(id).arity
    }
}

/// A static array of `Copy` records with `&'static str` names, read only
/// through a field that is not a name: no string comparison and no returned
/// reference.
pub mod static_str_table {
    #[derive(Clone, Copy)]
    pub enum TableId {
        Sin,
        Rootn,
    }

    #[derive(Clone, Copy)]
    pub struct NamedArity {
        pub name: &'static str,
        pub arity: usize,
    }

    pub static TABLE: [NamedArity; 2] = [
        NamedArity {
            name: "sin",
            arity: 1,
        },
        NamedArity {
            name: "rootn",
            arity: 2,
        },
    ];

    pub fn arity(id: TableId) -> usize {
        match id {
            TableId::Sin => TABLE[0].arity,
            TableId::Rootn => TABLE[1].arity,
        }
    }
}

/// A string literal returned from a function as `&'static str`.
pub mod string_literal_return {
    #[derive(Clone, Copy)]
    pub enum FunctionId {
        Sin,
        Exp,
    }

    pub fn name(id: FunctionId) -> &'static str {
        match id {
            FunctionId::Sin => "sin",
            FunctionId::Exp => "exp",
        }
    }
}

/// A `match` on string literals.
pub mod string_match {
    #[derive(Clone, Copy)]
    pub enum FunctionId {
        Sin,
        Exp,
    }

    pub fn lookup(name: &str) -> Option<FunctionId> {
        match name {
            "sin" => Some(FunctionId::Sin),
            "exp" => Some(FunctionId::Exp),
            _ => None,
        }
    }
}

/// A cast of a fieldless enumeration to an array index.
pub mod enum_index_cast {
    #[derive(Clone, Copy)]
    pub enum FunctionId {
        Sin,
        Exp,
        Log,
    }

    pub const ARITIES: [usize; 3] = [1, 1, 1];

    pub fn arity(id: FunctionId) -> usize {
        ARITIES[id as usize]
    }
}

/// Function pointers stored in a constant table and called through it.
pub mod function_pointers {
    fn halve(x: u64) -> u64 {
        x / 2
    }

    fn double(x: u64) -> u64 {
        x.wrapping_mul(2)
    }

    pub struct Entry {
        pub evaluate: fn(u64) -> u64,
    }

    pub const ENTRIES: [Entry; 2] = [Entry { evaluate: halve }, Entry { evaluate: double }];

    pub fn apply(index: usize, x: u64) -> u64 {
        (ENTRIES[index].evaluate)(x)
    }
}

/// A shared series summer: a generic trait whose hooks take `&mut self` and
/// the budget and return `Result`, driven by one `while` loop that calls them
/// with `?` and returns a partial-sum record from inside the loop. The hooks
/// of the implementation convert a failed charge into a halt with `?`.
pub mod series_summer {
    use crate::budget::{Budget, Exhausted};

    /// Why a summation stopped without a partial sum.
    pub enum Halt {
        Exhausted,
        IterationLimit,
    }

    impl From<Exhausted> for Halt {
        fn from(_: Exhausted) -> Self {
            Halt::Exhausted
        }
    }

    pub struct PartialSum {
        pub sum: u64,
        pub tail: u64,
        pub steps: usize,
    }

    pub(crate) trait Series {
        /// The candidate term of step `index`.
        fn term(&mut self, index: usize, budget: &mut Budget) -> Result<u64, Halt>;
        /// A bound on the remainder after the partial sum held before the step.
        fn tail(&self, index: usize, term: u64, budget: &mut Budget) -> Result<u64, Halt>;
        fn accumulate(&self, sum: u64, term: u64, budget: &mut Budget) -> Result<u64, Halt>;
        fn advance(&mut self, index: usize, budget: &mut Budget) -> Result<(), Halt>;
    }

    pub(crate) fn sum_series<S: Series>(
        series: &mut S,
        initial: u64,
        threshold: u64,
        maximum: usize,
        budget: &mut Budget,
    ) -> Result<PartialSum, Halt> {
        let mut sum = initial;
        let mut index = 0;
        while index < maximum {
            let term = series.term(index, budget)?;
            let tail = series.tail(index, term, budget)?;
            if tail <= threshold {
                return Ok(PartialSum {
                    sum,
                    tail,
                    steps: index + 1,
                });
            }
            sum = series.accumulate(sum, term, budget)?;
            series.advance(index, budget)?;
            index += 1;
        }
        Err(Halt::IterationLimit)
    }

    /// The candidates `t/2, t/4, ...` in integer arithmetic; the tail hook
    /// returns the candidate itself.
    pub struct Halving {
        pub term: u64,
    }

    impl Series for Halving {
        fn term(&mut self, _index: usize, budget: &mut Budget) -> Result<u64, Halt> {
            budget.take(1)?;
            Ok(self.term / 2)
        }

        fn tail(&self, _index: usize, term: u64, _budget: &mut Budget) -> Result<u64, Halt> {
            Ok(term)
        }

        fn accumulate(&self, sum: u64, term: u64, budget: &mut Budget) -> Result<u64, Halt> {
            budget.take(1)?;
            Ok(sum + term)
        }

        fn advance(&mut self, _index: usize, _budget: &mut Budget) -> Result<(), Halt> {
            self.term /= 2;
            Ok(())
        }
    }

    pub fn sum_halving(
        start: u64,
        threshold: u64,
        maximum: usize,
        budget: &mut Budget,
    ) -> Result<PartialSum, Halt> {
        let mut series = Halving { term: start };
        sum_series(&mut series, start, threshold, maximum, budget)
    }
}

/// `?` converting one error type into another through a `From`
/// implementation, and the conversion of a halt into a result state.
pub mod error_conversion {
    use crate::meter::{Failure, Meter};

    pub enum Halt {
        Failed(Failure),
        IterationLimit,
    }

    impl From<Failure> for Halt {
        fn from(failure: Failure) -> Self {
            Halt::Failed(failure)
        }
    }

    pub enum Bounded {
        Complete(u32),
        IterationLimit,
    }

    pub fn charge_steps(meter: &mut Meter, steps: u32, maximum: u32) -> Result<u32, Halt> {
        let mut done = 0;
        while done < steps {
            if done == maximum {
                return Err(Halt::IterationLimit);
            }
            meter.charge(1)?;
            done += 1;
        }
        Ok(done)
    }

    pub fn settle(run: Result<u32, Halt>) -> Result<Bounded, Failure> {
        match run {
            Ok(value) => Ok(Bounded::Complete(value)),
            Err(Halt::IterationLimit) => Ok(Bounded::IterationLimit),
            Err(Halt::Failed(failure)) => Err(failure),
        }
    }
}

/// Iteration over an ordered map in increasing key order.
pub mod map_iteration {
    use std::collections::BTreeMap;

    /// An order-dependent fold over the entries.
    pub fn fold(map: &BTreeMap<u32, u64>) -> u64 {
        let mut total = 0u64;
        for (&key, value) in map.iter() {
            total = total.wrapping_mul(31).wrapping_add(u64::from(key) ^ *value);
        }
        total
    }
}

/// Iteration over an ordered map in decreasing key order.
pub mod map_reverse_iteration {
    use std::collections::BTreeMap;

    pub fn fold(map: &BTreeMap<u32, u64>) -> u64 {
        let mut total = 0u64;
        for (&key, value) in map.iter().rev() {
            total = total.wrapping_mul(31).wrapping_add(u64::from(key) ^ *value);
        }
        total
    }
}

/// Iteration over an ordered map in decreasing key order by calling
/// `next_back` on the iterator, without the `rev` adapter.
pub mod map_next_back {
    use std::collections::BTreeMap;

    pub fn fold(map: &BTreeMap<u32, u64>) -> u64 {
        let mut total = 0u64;
        let mut entries = map.iter();
        while let Some((&key, value)) = entries.next_back() {
            total = total.wrapping_mul(31).wrapping_add(u64::from(key) ^ *value);
        }
        total
    }
}

/// The entry interface of an ordered map, as sparse coefficient accumulation
/// uses it: an occupied entry is updated or removed, a vacant one filled.
pub mod map_entry {
    use std::collections::BTreeMap;
    use std::collections::btree_map::Entry;

    pub fn accumulate(map: &mut BTreeMap<u32, u64>, key: u32, amount: u64) {
        match map.entry(key) {
            Entry::Occupied(mut entry) => {
                let value = entry.get_mut();
                *value = value.wrapping_add(amount);
                if *entry.get() == 0 {
                    entry.remove();
                }
            }
            Entry::Vacant(entry) => {
                if amount != 0 {
                    entry.insert(amount);
                }
            }
        }
    }
}

/// The degree and leading coefficient of a sparse polynomial from the last
/// entry of an ordered map, returned by value.
pub mod map_last {
    use std::collections::BTreeMap;

    pub fn degree(map: &BTreeMap<u32, u64>) -> Option<u32> {
        let mut degree = None;
        if let Some((&last, _)) = map.last_key_value() {
            degree = Some(last);
        }
        degree
    }

    pub fn leading(map: &BTreeMap<u32, u64>) -> u64 {
        match map.last_key_value() {
            Some((_, &value)) => value,
            None => 0,
        }
    }
}

/// A `for` loop over an ordered map that charges with `?` and updates a
/// second map through its entry interface, removing zeros, as adding a
/// shifted multiple of a sparse polynomial does.
pub mod map_loop_charge {
    use crate::budget::{Budget, Exhausted};
    use std::collections::BTreeMap;
    use std::collections::btree_map::Entry;

    pub fn add_shifted(
        target: &mut BTreeMap<u32, u64>,
        source: &BTreeMap<u32, u64>,
        shift: u32,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        for (&degree, &value) in source.iter() {
            budget.take(1)?;
            match target.entry(degree.wrapping_add(shift)) {
                Entry::Occupied(mut entry) => {
                    let sum = entry.get_mut();
                    *sum = sum.wrapping_add(value);
                    if *entry.get() == 0 {
                        entry.remove();
                    }
                }
                Entry::Vacant(entry) => {
                    if value != 0 {
                        entry.insert(value);
                    }
                }
            }
        }
        Ok(())
    }
}

/// A loop over an ordered map in decreasing key order with `next_back` that
/// charges with `?`, as Horner evaluation of a sparse polynomial does.
pub mod map_next_back_charge {
    use crate::budget::{Budget, Exhausted};
    use std::collections::BTreeMap;

    pub fn fold(
        map: &BTreeMap<u32, u64>,
        point: u64,
        budget: &mut Budget,
    ) -> Result<u64, Exhausted> {
        let mut total = 0u64;
        let mut entries = map.iter();
        while let Some((&degree, &value)) = entries.next_back() {
            budget.take(1)?;
            total = total
                .wrapping_mul(point)
                .wrapping_add(u64::from(degree) ^ value);
        }
        Ok(total)
    }
}

/// A polynomial interface whose access methods return a coefficient borrowed
/// from the polynomial as `Option<(u32, &'p E)>`, as the shared univariate
/// algorithms use it. Each generic loop carries only the degree of the last
/// visited term and takes the next borrow in its condition: a walk that
/// charges with `?` for every term, and a loop that replaces every visited
/// coefficient through a `&mut` method. A match guard on the borrowed leading
/// term, and a default method that selects between a copying and an in-place
/// loop. One implementation over dense vectors.
pub mod term_walk {
    use crate::budget::{Budget, Exhausted};

    pub(crate) trait Terms {
        type Element;
        type Poly: Clone;

        /// None for the zero polynomial.
        fn degree(&self, p: &Self::Poly) -> Option<u32>;
        /// The highest term, with its coefficient borrowed from `p`.
        fn leading_term<'p>(&self, p: &'p Self::Poly) -> Option<(u32, &'p Self::Element)>;
        /// The term after the term of degree `after`, or the first term when
        /// `after` is none, with its coefficient borrowed from `p`.
        fn term_after<'p>(
            &self,
            p: &'p Self::Poly,
            after: Option<u32>,
        ) -> Option<(u32, &'p Self::Element)>;
        fn visit(
            &self,
            total: &mut u64,
            degree: u32,
            coefficient: &Self::Element,
            budget: &mut Budget,
        ) -> Result<(), Exhausted>;
        fn halve(&self, a: &Self::Element, budget: &mut Budget)
        -> Result<Self::Element, Exhausted>;
        fn set(
            &self,
            p: &mut Self::Poly,
            degree: u32,
            value: Self::Element,
            budget: &mut Budget,
        ) -> Result<(), Exhausted>;
        fn replace(&self, p: &mut Self::Poly, degree: u32, value: Self::Element);
        fn in_place(&self) -> bool {
            false
        }
    }

    /// The term after the term of degree `after`; every walk ends at the term
    /// of degree `last`.
    fn next_term<'p, R: Terms>(
        ring: &R,
        p: &'p R::Poly,
        after: Option<u32>,
        last: Option<u32>,
    ) -> Option<(u32, &'p R::Element)> {
        match (after, last) {
            (Some(after), Some(last)) if after == last => None,
            _ => ring.term_after(p, after),
        }
    }

    pub(crate) fn fold<R: Terms>(
        ring: &R,
        p: &R::Poly,
        budget: &mut Budget,
    ) -> Result<u64, Exhausted> {
        let mut total = 0u64;
        let last = ring.degree(p);
        let mut after = None;
        while let Some((degree, coefficient)) = next_term(ring, p, after, last) {
            ring.visit(&mut total, degree, coefficient, budget)?;
            after = Some(degree);
        }
        Ok(total)
    }

    /// Halves every coefficient of a borrowed polynomial into a copy.
    pub(crate) fn halve_copy<R: Terms>(
        ring: &R,
        p: &R::Poly,
        budget: &mut Budget,
    ) -> Result<R::Poly, Exhausted> {
        let mut result = p.clone();
        let last = ring.degree(p);
        let mut after = None;
        while let Some((degree, coefficient)) = next_term(ring, p, after, last) {
            let value = ring.halve(coefficient, budget)?;
            ring.set(&mut result, degree, value, budget)?;
            after = Some(degree);
        }
        Ok(result)
    }

    /// Halves every coefficient of an owned polynomial in place.
    pub(crate) fn halve_in_place<R: Terms>(
        ring: &R,
        p: R::Poly,
        budget: &mut Budget,
    ) -> Result<R::Poly, Exhausted> {
        let mut p = p;
        let last = ring.degree(&p);
        let mut after = None;
        while let Some((degree, coefficient)) = next_term(ring, &p, after, last) {
            let value = ring.halve(coefficient, budget)?;
            ring.replace(&mut p, degree, value);
            after = Some(degree);
        }
        Ok(p)
    }

    pub(crate) fn halve<R: Terms>(
        ring: &R,
        p: R::Poly,
        budget: &mut Budget,
    ) -> Result<R::Poly, Exhausted> {
        if ring.in_place() {
            halve_in_place(ring, p, budget)
        } else {
            halve_copy(ring, &p, budget)
        }
    }

    /// The leading term when its degree is at least `bound`.
    fn reducible<'p, R: Terms>(
        ring: &R,
        p: &'p R::Poly,
        bound: u32,
    ) -> Option<(u32, &'p R::Element)> {
        match ring.leading_term(p) {
            Some((degree, leading)) if degree >= bound => Some((degree, leading)),
            _ => None,
        }
    }

    pub(crate) fn top<R: Terms>(
        ring: &R,
        p: &R::Poly,
        bound: u32,
        budget: &mut Budget,
    ) -> Result<u64, Exhausted> {
        let mut total = 0u64;
        if let Some((degree, leading)) = reducible(ring, p, bound) {
            ring.visit(&mut total, degree, leading, budget)?;
        }
        Ok(total)
    }

    /// Dense coefficient vectors, zeros included.
    pub struct Dense;

    impl Terms for Dense {
        type Element = u32;
        type Poly = Vec<u32>;

        fn degree(&self, p: &Vec<u32>) -> Option<u32> {
            if p.is_empty() {
                None
            } else {
                Some((p.len() - 1) as u32)
            }
        }

        fn leading_term<'p>(&self, p: &'p Vec<u32>) -> Option<(u32, &'p u32)> {
            if p.is_empty() {
                None
            } else {
                Some(((p.len() - 1) as u32, &p[p.len() - 1]))
            }
        }

        fn term_after<'p>(&self, p: &'p Vec<u32>, after: Option<u32>) -> Option<(u32, &'p u32)> {
            let index = match after {
                Some(degree) => degree as usize + 1,
                None => 0,
            };
            if index < p.len() {
                Some((index as u32, &p[index]))
            } else {
                None
            }
        }

        fn visit(
            &self,
            total: &mut u64,
            degree: u32,
            coefficient: &u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            budget.take(1)?;
            *total = total
                .wrapping_mul(31)
                .wrapping_add(u64::from(degree) ^ u64::from(*coefficient));
            Ok(())
        }

        fn halve(&self, a: &u32, budget: &mut Budget) -> Result<u32, Exhausted> {
            budget.take(1)?;
            Ok(*a / 2)
        }

        fn set(
            &self,
            p: &mut Vec<u32>,
            degree: u32,
            value: u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            budget.take(1)?;
            p[degree as usize] = value;
            Ok(())
        }

        fn replace(&self, p: &mut Vec<u32>, degree: u32, value: u32) {
            p[degree as usize] = value;
        }
    }

    pub fn fold_dense(p: &Vec<u32>, budget: &mut Budget) -> Result<u64, Exhausted> {
        fold(&Dense, p, budget)
    }

    pub fn halve_dense(p: Vec<u32>, budget: &mut Budget) -> Result<Vec<u32>, Exhausted> {
        halve(&Dense, p, budget)
    }

    pub fn halve_dense_in_place(p: Vec<u32>, budget: &mut Budget) -> Result<Vec<u32>, Exhausted> {
        halve_in_place(&Dense, p, budget)
    }

    pub fn top_dense(p: &Vec<u32>, bound: u32, budget: &mut Budget) -> Result<u64, Exhausted> {
        top(&Dense, p, bound, budget)
    }
}

/// The interface of `term_walk` over an ordered map, as a sparse polynomial
/// stores its nonzero terms: the first term from `first_key_value`, the
/// leading term from `last_key_value`, the next term from
/// `range((Excluded(degree), Unbounded)).next()`, and an in-place replacement
/// through `insert`.
pub mod map_term_walk {
    use crate::budget::{Budget, Exhausted};
    use crate::term_walk::{Terms, fold, halve, top};
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Unbounded};

    pub struct Sparse;

    impl Terms for Sparse {
        type Element = u64;
        type Poly = BTreeMap<u32, u64>;

        fn degree(&self, p: &BTreeMap<u32, u64>) -> Option<u32> {
            let mut degree = None;
            if let Some((&last, _)) = p.last_key_value() {
                degree = Some(last);
            }
            degree
        }

        fn leading_term<'p>(&self, p: &'p BTreeMap<u32, u64>) -> Option<(u32, &'p u64)> {
            match p.last_key_value() {
                Some((&degree, leading)) => Some((degree, leading)),
                None => None,
            }
        }

        fn term_after<'p>(
            &self,
            p: &'p BTreeMap<u32, u64>,
            after: Option<u32>,
        ) -> Option<(u32, &'p u64)> {
            let term = match after {
                Some(degree) => p.range((Excluded(degree), Unbounded)).next(),
                None => p.first_key_value(),
            };
            match term {
                Some((&degree, coefficient)) => Some((degree, coefficient)),
                None => None,
            }
        }

        fn visit(
            &self,
            total: &mut u64,
            degree: u32,
            coefficient: &u64,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            budget.take(1)?;
            *total = total
                .wrapping_mul(31)
                .wrapping_add(u64::from(degree) ^ *coefficient);
            Ok(())
        }

        fn halve(&self, a: &u64, budget: &mut Budget) -> Result<u64, Exhausted> {
            budget.take(1)?;
            Ok(*a / 2)
        }

        fn set(
            &self,
            p: &mut BTreeMap<u32, u64>,
            degree: u32,
            value: u64,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            budget.take(1)?;
            p.insert(degree, value);
            Ok(())
        }

        fn replace(&self, p: &mut BTreeMap<u32, u64>, degree: u32, value: u64) {
            p.insert(degree, value);
        }

        fn in_place(&self) -> bool {
            true
        }
    }

    pub fn fold_sparse(p: &BTreeMap<u32, u64>, budget: &mut Budget) -> Result<u64, Exhausted> {
        fold(&Sparse, p, budget)
    }

    pub fn halve_sparse(
        p: BTreeMap<u32, u64>,
        budget: &mut Budget,
    ) -> Result<BTreeMap<u32, u64>, Exhausted> {
        halve(&Sparse, p, budget)
    }

    pub fn top_sparse(
        p: &BTreeMap<u32, u64>,
        bound: u32,
        budget: &mut Budget,
    ) -> Result<u64, Exhausted> {
        top(&Sparse, p, bound, budget)
    }
}

/// The walk of `term_walk` with the borrowed term itself carried from one
/// iteration to the next instead of its degree.
pub mod carried_term_walk {
    use crate::budget::{Budget, Exhausted};
    use crate::term_walk::{Dense, Terms};

    pub(crate) fn fold<R: Terms>(
        ring: &R,
        p: &R::Poly,
        budget: &mut Budget,
    ) -> Result<u64, Exhausted> {
        let mut total = 0u64;
        let mut term = ring.term_after(p, None);
        while let Some((degree, coefficient)) = term {
            ring.visit(&mut total, degree, coefficient, budget)?;
            term = ring.term_after(p, Some(degree));
        }
        Ok(total)
    }

    pub fn fold_dense(p: &Vec<u32>, budget: &mut Budget) -> Result<u64, Exhausted> {
        fold(&Dense, p, budget)
    }
}

/// Monomials as ordered map keys, as multivariate polynomials keep them: a
/// copyable order tag with a data variant and derived comparisons; a key that
/// stores an exponent vector, its total degree and the tag, ordered by a
/// hand-written `Ord` that compares the tags and then dispatches by a `match`
/// to helpers, each with one index loop that returns from inside the loop; and
/// an ordered map keyed by it, updated with `insert` and `remove` and read
/// with `last_key_value`.
pub mod monomial_order {
    use std::cmp::Ordering;
    use std::collections::BTreeMap;

    #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
    #[non_exhaustive]
    pub enum TermOrder {
        Lex,
        GradedLex,
        GradedReverseLex,
        #[non_exhaustive]
        Block {
            first: usize,
        },
    }

    impl TermOrder {
        pub fn block(first: usize) -> Self {
            Self::Block { first }
        }
    }

    #[derive(Clone, Eq, PartialEq)]
    pub struct Term {
        pub powers: Vec<u32>,
        pub degree: u32,
        pub order: TermOrder,
    }

    impl Ord for Term {
        fn cmp(&self, other: &Self) -> Ordering {
            match self.order.cmp(&other.order) {
                Ordering::Equal => {}
                tags => return tags,
            }
            match self.order {
                TermOrder::Lex => compare_lex(&self.powers, &other.powers),
                TermOrder::GradedLex => match self.degree.cmp(&other.degree) {
                    Ordering::Equal => compare_lex(&self.powers, &other.powers),
                    degrees => degrees,
                },
                TermOrder::GradedReverseLex => match self.degree.cmp(&other.degree) {
                    Ordering::Equal => compare_reverse(&self.powers, &other.powers),
                    degrees => degrees,
                },
                TermOrder::Block { first } => compare_blocks(&self.powers, &other.powers, first),
            }
        }
    }

    impl PartialOrd for Term {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    fn compare_lex(a: &[u32], b: &[u32]) -> Ordering {
        let mut i = 0;
        while i < a.len() && i < b.len() {
            if a[i] != b[i] {
                return a[i].cmp(&b[i]);
            }
            i += 1;
        }
        a.len().cmp(&b.len())
    }

    fn compare_reverse(a: &[u32], b: &[u32]) -> Ordering {
        let mut i = a.len();
        let mut j = b.len();
        while i > 0 && j > 0 {
            i -= 1;
            j -= 1;
            if a[i] != b[j] {
                return b[j].cmp(&a[i]);
            }
        }
        b.len().cmp(&a.len())
    }

    fn compare_blocks(a: &[u32], b: &[u32], first: usize) -> Ordering {
        match a.len().cmp(&b.len()) {
            Ordering::Equal => {}
            lengths => return lengths,
        }
        let end = a.len();
        let split = if first < end { first } else { end };
        match compare_graded_reverse(a, b, 0, split) {
            Ordering::Equal => compare_graded_reverse(a, b, split, end),
            leading => leading,
        }
    }

    fn compare_graded_reverse(a: &[u32], b: &[u32], start: usize, end: usize) -> Ordering {
        match partial_degree(a, start, end).cmp(&partial_degree(b, start, end)) {
            Ordering::Equal => compare_reverse_range(a, b, start, end),
            degrees => degrees,
        }
    }

    fn partial_degree(a: &[u32], start: usize, end: usize) -> u64 {
        let mut total = 0u64;
        let mut i = start;
        while i < end {
            total += a[i] as u64;
            i += 1;
        }
        total
    }

    fn compare_reverse_range(a: &[u32], b: &[u32], start: usize, end: usize) -> Ordering {
        let mut i = end;
        while i > start {
            i -= 1;
            if a[i] != b[i] {
                return b[i].cmp(&a[i]);
            }
        }
        Ordering::Equal
    }

    /// Stores `value` as the coefficient of `term`, removing the term for
    /// zero, and returns the total degree of the greatest key.
    pub fn set_term(terms: &mut BTreeMap<Term, u64>, term: Term, value: u64) -> u32 {
        if value == 0 {
            terms.remove(&term);
        } else {
            terms.insert(term, value);
        }
        match terms.last_key_value() {
            Some((leading, _)) => leading.degree,
            None => 0,
        }
    }
}

/// A `for` loop over an integer range.
pub mod range_loop {
    pub fn total(count: u32) -> u64 {
        let mut total = 0u64;
        for index in 0..count {
            total += u64::from(index);
        }
        total
    }
}

/// A charge with `?` and an early `return` guarded by a comparison before a
/// loop that contains two `?`, as an evaluator validates its inputs and takes
/// a shortcut before its steps.
pub mod checks_before_loop {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_pairs(budget: &mut Budget, count: u32) -> Result<u32, Exhausted> {
        budget.take(1)?;
        if count == 0 {
            return Ok(0);
        }
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(done)
    }
}

/// An early `return` from a `match` on an `Option` before a loop that
/// contains two `?`.
pub mod return_before_loop {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_pairs(budget: &mut Budget, count: Option<u32>) -> Result<u32, Exhausted> {
        let mut done = 0;
        let count = match count {
            Some(count) => count,
            None => return Ok(done),
        };
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(done)
    }
}

/// An early `return` guarded by a flag that a `match` computes, before a loop
/// that contains two `?`.
pub mod flag_before_loop {
    use crate::budget::{Budget, Exhausted};

    #[derive(Clone, Copy)]
    pub enum Placement {
        Inside,
        Outside,
        Straddles,
    }

    pub fn charge_pairs(
        budget: &mut Budget,
        placement: Placement,
        count: u32,
    ) -> Result<u32, Exhausted> {
        let stop = match placement {
            Placement::Inside => false,
            Placement::Outside | Placement::Straddles => true,
        };
        if stop {
            return Ok(0);
        }
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(done)
    }
}

/// A loop with `?` inside the only branch of an `if let`, with nothing but the
/// return value after it.
pub mod loop_in_branch {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_each(budget: &mut Budget, count: Option<u32>) -> Result<u32, Exhausted> {
        let mut done = 0;
        if let Some(count) = count {
            while done < count {
                budget.take(1)?;
                done += 1;
            }
        }
        Ok(done)
    }
}

/// A `match` on a placement whose arms return early, before a loop that
/// contains two `?`.
pub mod placement_before_loop {
    use crate::budget::{Budget, Exhausted};

    #[derive(Clone, Copy)]
    pub enum Position {
        Inside,
        Outside,
        Straddles,
    }

    pub fn charge_pairs(
        budget: &mut Budget,
        position: Position,
        count: u32,
    ) -> Result<u32, Exhausted> {
        match position {
            Position::Inside => {}
            Position::Outside => return Ok(0),
            Position::Straddles => return Ok(1),
        }
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(done)
    }
}

/// The early returns of `return_before_loop` and `flag_before_loop`, and the
/// branch of `loop_in_branch`, in functions without a loop that hand the loop
/// with `?` to a helper, as an evaluator validates its inputs, places its
/// argument and takes its shortcuts before a summer runs the steps.
pub mod returns_then_helper {
    use crate::budget::{Budget, Exhausted};

    #[derive(Clone, Copy)]
    pub enum Region {
        Inside,
        Outside,
        Straddles,
    }

    pub fn evaluate(
        budget: &mut Budget,
        region: Region,
        count: Option<u32>,
    ) -> Result<u32, Exhausted> {
        budget.take(1)?;
        let stop = match region {
            Region::Inside => false,
            Region::Outside | Region::Straddles => true,
        };
        if stop {
            return Ok(0);
        }
        let count = match count {
            Some(count) => count,
            None => return Ok(0),
        };
        charge_pairs(budget, count)
    }

    pub fn charge_optional(budget: &mut Budget, count: Option<u32>) -> Result<u32, Exhausted> {
        let mut done = 0;
        if let Some(count) = count {
            done = charge_pairs(budget, count)?;
        }
        Ok(done)
    }

    fn charge_pairs(budget: &mut Budget, count: u32) -> Result<u32, Exhausted> {
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(done)
    }
}

/// A `match` arm with an integer literal inside an enumeration variant,
/// followed by a wildcard arm of the same variant, as the former call head of
/// a root mapped degree 2 to one record and every other degree to another.
pub mod literal_variant_match {
    #[derive(Clone, Copy)]
    pub enum PowerHead {
        Plain,
        Power(u32),
    }

    #[derive(Clone, Copy)]
    pub enum PowerKind {
        Plain,
        Square,
        Other,
    }

    pub fn kind(head: PowerHead) -> PowerKind {
        match head {
            PowerHead::Plain => PowerKind::Plain,
            PowerHead::Power(2) => PowerKind::Square,
            PowerHead::Power(_) => PowerKind::Other,
        }
    }
}

/// A `?` before a loop that contains two `?`, while the function owns a
/// vector, as a division owns its dividend when it checks its divisor.
pub mod owned_before_loop {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_pairs(
        values: Vec<u32>,
        budget: &mut Budget,
        count: u32,
    ) -> Result<Vec<u32>, Exhausted> {
        budget.take(1)?;
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(values)
    }
}

/// The function of `owned_before_loop` with its loop in a helper that leaves
/// no `?` before the loop, and the same function with one `?` in its loop.
pub mod owned_then_helper {
    use crate::budget::{Budget, Exhausted};

    pub fn charge_pairs(
        values: Vec<u32>,
        budget: &mut Budget,
        count: u32,
    ) -> Result<Vec<u32>, Exhausted> {
        budget.take(1)?;
        pairs(values, budget, count)
    }

    fn pairs(values: Vec<u32>, budget: &mut Budget, count: u32) -> Result<Vec<u32>, Exhausted> {
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            budget.take(1)?;
            done += 1;
        }
        Ok(values)
    }

    pub fn charge_each(
        values: Vec<u32>,
        budget: &mut Budget,
        count: u32,
    ) -> Result<Vec<u32>, Exhausted> {
        budget.take(1)?;
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            done += 1;
        }
        Ok(values)
    }
}

/// Coefficient maps whose outcome is a result state, in the forms of the
/// crate-private map framework of the library: a generic map result whose
/// variants both carry a payload; an uninhabited reason type for total maps,
/// whose results an exhaustive empty `match` unwraps; a trait with associated
/// source, target and reason types whose `apply` takes `&self`, a source
/// reference and a meter; a sink trait implemented for `Vec` and for an
/// accumulator that charges and bounds each entry; and two coefficientwise
/// maps with two `?` in their loop and a `match` that returns the state from
/// inside it: one over a slice in an index loop, and one over a term walk
/// from a sparse form into another polynomial form, here a borrowed view with
/// a lifetime parameter. The instances are a total residue map and a partial
/// narrowing whose membership test returns early, and whose reason a caller
/// turns into an error at its boundary. The names are unique among the
/// qualification modules.
pub mod coefficient_map {
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Unbounded};

    /// The reasons a value lies outside the domain of the narrowing.
    #[derive(Clone, Copy)]
    pub enum Outside {
        Negative,
        Large,
    }

    /// The failures of the meter, and the error of the boundary.
    #[derive(Clone, Copy)]
    pub enum MapFailure {
        Exhausted,
        OutsideDomain(Outside),
    }

    pub struct MapMeter {
        pub left: u64,
    }

    impl MapMeter {
        pub fn charge(&mut self, amount: u64) -> Result<(), MapFailure> {
            if amount > self.left {
                return Err(MapFailure::Exhausted);
            }
            self.left -= amount;
            Ok(())
        }
    }

    /// The outcome of a map: the image, or the state that the value lies
    /// outside the domain, with the reason.
    pub enum MapResult<T, R> {
        Mapped(T),
        NotInDomain(R),
    }

    /// The reason type of a total map: no value lies outside its domain.
    pub enum Total {}

    /// The image under a total map.
    pub fn total<T>(result: MapResult<T, Total>) -> T {
        match result {
            MapResult::Mapped(value) => value,
            MapResult::NotInDomain(never) => match never {},
        }
    }

    pub(crate) trait CoefficientMap {
        type Source;
        type Target;
        type Outside;

        fn apply(
            &self,
            value: &Self::Source,
            meter: &mut MapMeter,
        ) -> Result<MapResult<Self::Target, Self::Outside>, MapFailure>;
    }

    /// A container that receives images one at a time.
    pub(crate) trait Entries {
        type Entry;

        fn push_entry(
            &mut self,
            value: Self::Entry,
            meter: &mut MapMeter,
        ) -> Result<(), MapFailure>;
    }

    impl<T> Entries for Vec<T> {
        type Entry = T;

        fn push_entry(&mut self, value: T, _meter: &mut MapMeter) -> Result<(), MapFailure> {
            self.push(value);
            Ok(())
        }
    }

    /// An accumulator that charges each entry and bounds the running total.
    pub struct CappedEntries {
        pub entries: Vec<u32>,
        pub total: u64,
        pub cap: u64,
    }

    impl Entries for CappedEntries {
        type Entry = u32;

        fn push_entry(&mut self, value: u32, meter: &mut MapMeter) -> Result<(), MapFailure> {
            meter.charge(1)?;
            self.total = self.total.saturating_add(u64::from(value));
            if self.total > self.cap {
                return Err(MapFailure::Exhausted);
            }
            self.entries.push(value);
            Ok(())
        }
    }

    /// Maps `values` in order into `entries`; the first value outside the
    /// domain ends the map with its reason.
    pub(crate) fn map_entries<M: CoefficientMap, E: Entries<Entry = M::Target>>(
        map: &M,
        values: &[M::Source],
        entries: E,
        meter: &mut MapMeter,
    ) -> Result<MapResult<E, M::Outside>, MapFailure> {
        let mut entries = entries;
        let mut index = 0;
        while index < values.len() {
            match map.apply(&values[index], meter)? {
                MapResult::Mapped(value) => entries.push_entry(value, meter)?,
                MapResult::NotInDomain(outside) => return Ok(MapResult::NotInDomain(outside)),
            }
            index += 1;
        }
        Ok(MapResult::Mapped(entries))
    }

    /// Polynomial forms walked term by term.
    pub(crate) trait MapTerms {
        type Coefficient;
        type Form;

        fn degree(&self, p: &Self::Form) -> Option<u32>;
        fn term_after<'p>(
            &self,
            p: &'p Self::Form,
            after: Option<u32>,
        ) -> Option<(u32, &'p Self::Coefficient)>;
        fn set_coefficient(
            &self,
            p: &mut Self::Form,
            degree: u32,
            value: Self::Coefficient,
            meter: &mut MapMeter,
        ) -> Result<(), MapFailure>;
    }

    fn next_mapped_term<'p, R: MapTerms>(
        ring: &R,
        p: &'p R::Form,
        after: Option<u32>,
        last: Option<u32>,
    ) -> Option<(u32, &'p R::Coefficient)> {
        match (after, last) {
            (Some(after), Some(last)) if after == last => None,
            _ => ring.term_after(p, after),
        }
    }

    /// Maps the terms of `p`, a form of `source`, into `result`, a form of
    /// `target`; the first coefficient outside the domain ends the map.
    pub(crate) fn map_terms<M, S, T>(
        map: &M,
        source: &S,
        target: &T,
        p: &S::Form,
        result: T::Form,
        meter: &mut MapMeter,
    ) -> Result<MapResult<T::Form, M::Outside>, MapFailure>
    where
        M: CoefficientMap<Source = S::Coefficient, Target = T::Coefficient>,
        S: MapTerms,
        T: MapTerms,
    {
        let mut result = result;
        let last = source.degree(p);
        let mut after = None;
        while let Some((degree, coefficient)) = next_mapped_term(source, p, after, last) {
            match map.apply(coefficient, meter)? {
                MapResult::Mapped(value) => {
                    target.set_coefficient(&mut result, degree, value, meter)?
                }
                MapResult::NotInDomain(outside) => return Ok(MapResult::NotInDomain(outside)),
            }
            after = Some(degree);
        }
        Ok(MapResult::Mapped(result))
    }

    /// The total map from machine words onto residues modulo `p`.
    pub struct WordResidues {
        pub p: u32,
    }

    impl CoefficientMap for WordResidues {
        type Source = u64;
        type Target = u32;
        type Outside = Total;

        fn apply(
            &self,
            value: &u64,
            meter: &mut MapMeter,
        ) -> Result<MapResult<u32, Total>, MapFailure> {
            meter.charge(1)?;
            Ok(MapResult::Mapped((*value % u64::from(self.p)) as u32))
        }
    }

    /// The partial narrowing of signed words to unsigned words.
    pub struct Narrowing;

    /// Why `value` lies outside the domain of the narrowing, or none: a test
    /// with early returns, as a domain check is.
    fn narrowing_outside(value: &i64, meter: &mut MapMeter) -> Result<Option<Outside>, MapFailure> {
        meter.charge(1)?;
        if *value < 0 {
            return Ok(Some(Outside::Negative));
        }
        if *value > 4_294_967_295 {
            return Ok(Some(Outside::Large));
        }
        Ok(None)
    }

    impl CoefficientMap for Narrowing {
        type Source = i64;
        type Target = u32;
        type Outside = Outside;

        fn apply(
            &self,
            value: &i64,
            meter: &mut MapMeter,
        ) -> Result<MapResult<u32, Outside>, MapFailure> {
            match narrowing_outside(value, meter)? {
                None => Ok(MapResult::Mapped(*value as u32)),
                Some(outside) => Ok(MapResult::NotInDomain(outside)),
            }
        }
    }

    /// Sparse forms with word coefficients.
    pub struct SparseWords;

    /// The term of `p` after the term of degree `after`, or its first term.
    fn sparse_term_after<C>(p: &BTreeMap<u32, C>, after: Option<u32>) -> Option<(u32, &C)> {
        let term = match after {
            Some(degree) => p.range((Excluded(degree), Unbounded)).next(),
            None => p.first_key_value(),
        };
        match term {
            Some((&degree, coefficient)) => Some((degree, coefficient)),
            None => None,
        }
    }

    /// The degree of a sparse form; none for zero.
    fn sparse_degree<C>(p: &BTreeMap<u32, C>) -> Option<u32> {
        let mut degree = None;
        if let Some((&last, _)) = p.last_key_value() {
            degree = Some(last);
        }
        degree
    }

    impl MapTerms for SparseWords {
        type Coefficient = u64;
        type Form = BTreeMap<u32, u64>;

        fn degree(&self, p: &BTreeMap<u32, u64>) -> Option<u32> {
            sparse_degree(p)
        }

        fn term_after<'p>(
            &self,
            p: &'p BTreeMap<u32, u64>,
            after: Option<u32>,
        ) -> Option<(u32, &'p u64)> {
            sparse_term_after(p, after)
        }

        fn set_coefficient(
            &self,
            p: &mut BTreeMap<u32, u64>,
            degree: u32,
            value: u64,
            meter: &mut MapMeter,
        ) -> Result<(), MapFailure> {
            meter.charge(1)?;
            p.insert(degree, value);
            Ok(())
        }
    }

    /// A borrowed view of a residue ring: sparse forms with residue
    /// coefficients. Its methods keep to `?` and calls.
    pub struct ResidueView<'a> {
        pub p: &'a u32,
    }

    impl MapTerms for ResidueView<'_> {
        type Coefficient = u32;
        type Form = BTreeMap<u32, u32>;

        fn degree(&self, p: &BTreeMap<u32, u32>) -> Option<u32> {
            sparse_degree(p)
        }

        fn term_after<'p>(
            &self,
            p: &'p BTreeMap<u32, u32>,
            after: Option<u32>,
        ) -> Option<(u32, &'p u32)> {
            sparse_term_after(p, after)
        }

        fn set_coefficient(
            &self,
            p: &mut BTreeMap<u32, u32>,
            degree: u32,
            value: u32,
            meter: &mut MapMeter,
        ) -> Result<(), MapFailure> {
            meter.charge(1)?;
            p.insert(degree, value);
            Ok(())
        }
    }

    /// The residues of `values`, through the total map.
    pub fn reduce_words(
        p: u32,
        values: &[u64],
        meter: &mut MapMeter,
    ) -> Result<Vec<u32>, MapFailure> {
        let residues = WordResidues { p };
        let result = map_entries(&residues, values, Vec::new(), meter)?;
        Ok(total(result))
    }

    /// The narrowing of `values` into a capped accumulator, as a state.
    pub fn narrow_capped(
        values: &[i64],
        cap: u64,
        meter: &mut MapMeter,
    ) -> Result<MapResult<CappedEntries, Outside>, MapFailure> {
        meter.charge(1)?;
        let entries = CappedEntries {
            entries: Vec::new(),
            total: 0,
            cap,
        };
        map_entries(&Narrowing, values, entries, meter)
    }

    /// The narrowing of `values`, with a value outside the domain reported
    /// as an error at the boundary.
    pub fn narrow_or_fail(values: &[i64], meter: &mut MapMeter) -> Result<Vec<u32>, MapFailure> {
        meter.charge(1)?;
        match map_entries(&Narrowing, values, Vec::new(), meter)? {
            MapResult::Mapped(entries) => Ok(entries),
            MapResult::NotInDomain(outside) => Err(MapFailure::OutsideDomain(outside)),
        }
    }

    /// The residues of the coefficients of `p`, mapped term by term into a
    /// form of the borrowed view.
    pub fn reduce_terms(
        p: &u32,
        source: &BTreeMap<u32, u64>,
        meter: &mut MapMeter,
    ) -> Result<BTreeMap<u32, u32>, MapFailure> {
        let view = ResidueView { p };
        let residues = WordResidues { p: *p };
        let result = map_terms(
            &residues,
            &SparseWords,
            &view,
            source,
            BTreeMap::new(),
            meter,
        )?;
        Ok(total(result))
    }

    /// The narrowing of the coefficients of `p`, term by term, as a state.
    pub fn narrow_terms(
        source: &BTreeMap<u32, i64>,
        meter: &mut MapMeter,
    ) -> Result<MapResult<BTreeMap<u32, u32>, Outside>, MapFailure> {
        let bound = u32::MAX;
        let view = ResidueView { p: &bound };
        map_terms(
            &Narrowing,
            &SignedWords,
            &view,
            source,
            BTreeMap::new(),
            meter,
        )
    }

    /// Sparse forms with signed word coefficients.
    pub struct SignedWords;

    impl MapTerms for SignedWords {
        type Coefficient = i64;
        type Form = BTreeMap<u32, i64>;

        fn degree(&self, p: &BTreeMap<u32, i64>) -> Option<u32> {
            sparse_degree(p)
        }

        fn term_after<'p>(
            &self,
            p: &'p BTreeMap<u32, i64>,
            after: Option<u32>,
        ) -> Option<(u32, &'p i64)> {
            sparse_term_after(p, after)
        }

        fn set_coefficient(
            &self,
            p: &mut BTreeMap<u32, i64>,
            degree: u32,
            value: i64,
            meter: &mut MapMeter,
        ) -> Result<(), MapFailure> {
            meter.charge(1)?;
            p.insert(degree, value);
            Ok(())
        }
    }
}

/// A method of an implementation that calls a default method of its own
/// trait, which the implementation keeps, as a hook of the shared univariate
/// interface that takes the default divisor form would. The trait is a
/// subtrait written with a `where` clause, as that interface is.
///
/// The expected Lean error is "Unknown constant
/// `...SelfCallSeven.Insts.Formal_qualificationDefault_self_callSelfCallDivisorsU8`"
/// in the definition of `charged_divisor`: it applies the default `divisor`
/// to the implementation, whose definition Lean only reaches after the
/// method. Qualification checks only that the module is ill-typed, so a
/// review of a requalification compares the log with this error.
pub mod default_self_call {
    use crate::budget::{Budget, Exhausted};

    pub(crate) trait SelfCallUnits {
        type Element;

        fn reduce(
            &self,
            a: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted>;
    }

    pub(crate) trait SelfCallDivisors
    where
        Self: SelfCallUnits,
    {
        /// The divisor form of `d`: by default the reduced element.
        fn divisor(
            &self,
            d: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted> {
            self.reduce(d, budget)
        }

        /// One charge, then the divisor form of `d`.
        fn charged_divisor(
            &self,
            d: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted>;
    }

    /// Residues modulo 7 in a byte.
    pub struct SelfCallSeven;

    impl SelfCallUnits for SelfCallSeven {
        type Element = u8;

        fn reduce(&self, a: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            Ok(*a % 7)
        }
    }

    impl SelfCallDivisors for SelfCallSeven {
        fn charged_divisor(&self, d: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            self.divisor(d, budget)
        }
    }

    pub fn charged_divisor_seven(d: u8, budget: &mut Budget) -> Result<u8, Exhausted> {
        SelfCallSeven.charged_divisor(&d, budget)
    }
}

/// The traits of `default_self_call` with the implementation's method calling
/// the body of the default method instead of the method itself. A second
/// default method calls the first, as the default monic hook of the shared
/// univariate interface calls the default divisor form; the implementation
/// keeps both, and a generic function calls the second through the trait.
pub mod default_direct_call {
    use crate::budget::{Budget, Exhausted};

    pub(crate) trait DirectCallUnits {
        type Element;

        fn reduce(
            &self,
            a: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted>;
    }

    pub(crate) trait DirectCallDivisors
    where
        Self: DirectCallUnits,
    {
        /// The divisor form of `d`: by default the reduced element.
        fn divisor(
            &self,
            d: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted> {
            self.reduce(d, budget)
        }

        /// One charge, then the divisor form of `d`: by default through
        /// `divisor`.
        fn checked_divisor(
            &self,
            d: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted> {
            budget.take(1)?;
            self.divisor(d, budget)
        }

        /// One charge, then the divisor form of `d`.
        fn charged_divisor(
            &self,
            d: &Self::Element,
            budget: &mut Budget,
        ) -> Result<Self::Element, Exhausted>;
    }

    /// Residues modulo 7 in a byte.
    pub struct DirectCallSeven;

    impl DirectCallUnits for DirectCallSeven {
        type Element = u8;

        fn reduce(&self, a: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            Ok(*a % 7)
        }
    }

    impl DirectCallDivisors for DirectCallSeven {
        // The body of the default `divisor`, not a call of it.
        fn charged_divisor(&self, d: &u8, budget: &mut Budget) -> Result<u8, Exhausted> {
            budget.take(1)?;
            self.reduce(d, budget)
        }
    }

    pub(crate) fn checked<R: DirectCallDivisors>(
        ring: &R,
        d: &R::Element,
        budget: &mut Budget,
    ) -> Result<R::Element, Exhausted> {
        ring.checked_divisor(d, budget)
    }

    pub fn charged_divisor_seven(d: u8, budget: &mut Budget) -> Result<u8, Exhausted> {
        DirectCallSeven.charged_divisor(&d, budget)
    }

    pub fn checked_divisor_seven(d: u8, budget: &mut Budget) -> Result<u8, Exhausted> {
        checked(&DirectCallSeven, &d, budget)
    }
}

/// A method of an implementation for a borrowed view, whose type has a
/// lifetime parameter, with a `for` loop over `BTreeMap::iter` that charges
/// with `?`, as adding a product row over a number field does. Aeneas stops
/// with an internal error because a loop joins control flow in a function that
/// takes the view by reference; the map and the `?` play no part
/// (`view_index_loop`).
pub mod view_map_loop {
    use crate::budget::{Budget, Exhausted};
    use std::collections::BTreeMap;

    pub(crate) trait LoopRows {
        type Element;
        type Poly;

        /// Adds the terms of `other`, shifted by `shift`, to `result`.
        fn add_row(
            &self,
            result: &mut Self::Poly,
            other: &Self::Poly,
            shift: u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted>;
    }

    pub struct LoopView<'a> {
        pub name: &'a str,
    }

    impl LoopRows for LoopView<'_> {
        type Element = u64;
        type Poly = BTreeMap<u32, u64>;

        fn add_row(
            &self,
            result: &mut BTreeMap<u32, u64>,
            other: &BTreeMap<u32, u64>,
            shift: u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            for (&degree, &value) in other.iter() {
                budget.take(1)?;
                result.insert(degree.wrapping_add(shift), value);
            }
            Ok(())
        }
    }

    pub fn add_row_view(
        view: &LoopView<'_>,
        result: &mut BTreeMap<u32, u64>,
        other: &BTreeMap<u32, u64>,
        shift: u32,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        view.add_row(result, other, shift, budget)
    }
}

/// A method of an implementation for a borrowed view, whose type has a
/// lifetime parameter, that returns the term after a given key with
/// `range((Excluded(key), Unbounded)).next()`, as the number-field term walk
/// does. The loop-free form of `view_map_loop`. Aeneas stops with an internal
/// error at the first `match`, whose arms meet again before the second one;
/// such a join fails in a function that takes the view by reference whatever
/// the arms compute (`view_value_join`).
pub mod view_map_range {
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Unbounded};

    pub(crate) trait RangeTerms {
        type Element;
        type Poly;

        /// The term after the term of degree `after`, or the first term when
        /// `after` is none, with its coefficient borrowed from `p`.
        fn term_after<'p>(
            &self,
            p: &'p Self::Poly,
            after: Option<u32>,
        ) -> Option<(u32, &'p Self::Element)>;
    }

    pub struct RangeView<'a> {
        pub name: &'a str,
    }

    impl RangeTerms for RangeView<'_> {
        type Element = u64;
        type Poly = BTreeMap<u32, u64>;

        fn term_after<'p>(
            &self,
            p: &'p BTreeMap<u32, u64>,
            after: Option<u32>,
        ) -> Option<(u32, &'p u64)> {
            let term = match after {
                Some(degree) => p.range((Excluded(degree), Unbounded)).next(),
                None => p.first_key_value(),
            };
            match term {
                Some((&degree, coefficient)) => Some((degree, coefficient)),
                None => None,
            }
        }
    }

    pub fn term_after_view<'p>(
        view: &RangeView<'_>,
        p: &'p BTreeMap<u32, u64>,
        after: Option<u32>,
    ) -> Option<(u32, &'p u64)> {
        view.term_after(p, after)
    }
}

/// A method of an implementation for a borrowed view, whose type has a
/// lifetime parameter, with an index `while` loop over a slice that uses
/// neither a map nor `?`. It fails as `view_map_loop` does.
pub mod view_index_loop {
    pub(crate) trait IndexSums {
        /// The wrapping sum of `values`.
        fn sum(&self, values: &[u64]) -> u64;
    }

    pub struct IndexView<'a> {
        pub name: &'a str,
    }

    impl IndexSums for IndexView<'_> {
        fn sum(&self, values: &[u64]) -> u64 {
            let mut index = 0;
            let mut total = 0u64;
            while index < values.len() {
                total = total.wrapping_add(values[index]);
                index += 1;
            }
            total
        }
    }

    pub fn sum_view(view: &IndexView<'_>, values: &[u64]) -> u64 {
        view.sum(values)
    }
}

/// An inherent method of a borrowed view, whose type has a lifetime
/// parameter, with a `match` on an `Option<u32>` whose arms compute a plain
/// value that the method then uses. It fails as the first `match` of
/// `view_map_range` does, without any borrow in the arms.
pub mod view_value_join {
    pub struct JoinView<'a> {
        pub name: &'a str,
    }

    impl JoinView<'_> {
        /// Three times the degree after `after`, or zero.
        pub fn scaled_next(&self, after: Option<u32>) -> u32 {
            let next = match after {
                Some(degree) => degree.wrapping_add(1),
                None => 0,
            };
            next.wrapping_mul(3)
        }
    }
}

/// The method of `view_index_loop` delegating to a free function that holds
/// the loop and takes the view by reference, as a method that passes `self`
/// on would. The free function fails as the method does.
pub mod view_borrowed_helper {
    pub(crate) trait BorrowedSums {
        /// The wrapping sum of `values`.
        fn sum(&self, values: &[u64]) -> u64;
    }

    pub struct BorrowedView<'a> {
        pub name: &'a str,
    }

    fn sum_values(_view: &BorrowedView<'_>, values: &[u64]) -> u64 {
        let mut index = 0;
        let mut total = 0u64;
        while index < values.len() {
            total = total.wrapping_add(values[index]);
            index += 1;
        }
        total
    }

    impl BorrowedSums for BorrowedView<'_> {
        fn sum(&self, values: &[u64]) -> u64 {
            sum_values(self, values)
        }
    }

    pub fn sum_view(view: &BorrowedView<'_>, values: &[u64]) -> u64 {
        view.sum(values)
    }
}

/// The methods of `view_map_loop` and `view_map_range` for a borrowed view,
/// each delegating to a free function that holds the iterator code and does
/// not take the view.
pub mod view_map_helper {
    use crate::budget::{Budget, Exhausted};
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Unbounded};

    pub(crate) trait HelperTerms {
        type Element;
        type Poly;

        /// Adds the terms of `other`, shifted by `shift`, to `result`.
        fn add_row(
            &self,
            result: &mut Self::Poly,
            other: &Self::Poly,
            shift: u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted>;

        /// The term after the term of degree `after`, or the first term when
        /// `after` is none, with its coefficient borrowed from `p`.
        fn term_after<'p>(
            &self,
            p: &'p Self::Poly,
            after: Option<u32>,
        ) -> Option<(u32, &'p Self::Element)>;
    }

    pub struct HelperView<'a> {
        pub name: &'a str,
    }

    fn add_shifted(
        result: &mut BTreeMap<u32, u64>,
        other: &BTreeMap<u32, u64>,
        shift: u32,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        for (&degree, &value) in other.iter() {
            budget.take(1)?;
            result.insert(degree.wrapping_add(shift), value);
        }
        Ok(())
    }

    fn stored_term_after(p: &BTreeMap<u32, u64>, after: Option<u32>) -> Option<(u32, &u64)> {
        let term = match after {
            Some(degree) => p.range((Excluded(degree), Unbounded)).next(),
            None => p.first_key_value(),
        };
        match term {
            Some((&degree, coefficient)) => Some((degree, coefficient)),
            None => None,
        }
    }

    impl HelperTerms for HelperView<'_> {
        type Element = u64;
        type Poly = BTreeMap<u32, u64>;

        fn add_row(
            &self,
            result: &mut BTreeMap<u32, u64>,
            other: &BTreeMap<u32, u64>,
            shift: u32,
            budget: &mut Budget,
        ) -> Result<(), Exhausted> {
            add_shifted(result, other, shift, budget)
        }

        fn term_after<'p>(
            &self,
            p: &'p BTreeMap<u32, u64>,
            after: Option<u32>,
        ) -> Option<(u32, &'p u64)> {
            stored_term_after(p, after)
        }
    }

    pub fn add_row_view(
        view: &HelperView<'_>,
        result: &mut BTreeMap<u32, u64>,
        other: &BTreeMap<u32, u64>,
        shift: u32,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        view.add_row(result, other, shift, budget)
    }

    pub fn term_after_view<'p>(
        view: &HelperView<'_>,
        p: &'p BTreeMap<u32, u64>,
        after: Option<u32>,
    ) -> Option<(u32, &'p u64)> {
        view.term_after(p, after)
    }
}

/// A second static table of plain records next to a registry, keyed by the
/// same kind of identifier: fieldless enumeration fields and an array field
/// of enumerations, a copy of a record through an exhaustive `match`, dispatch
/// by `match` on a field of the copy, and an element of its array field read
/// at an index computed from an argument with `%` and `as usize`.
pub mod registry_items {
    #[derive(Clone, Copy)]
    pub enum ItemOwner {
        Sine,
        Cosine,
        Logarithm,
    }

    #[derive(Clone, Copy)]
    pub enum TurnFamily {
        Absent,
        QuarterTurns,
    }

    #[derive(Clone, Copy)]
    pub enum TurnValue {
        Absent,
        Zero,
        One,
        MinusOne,
        Undefined,
    }

    #[derive(Clone, Copy)]
    pub struct ItemRecord {
        pub family: TurnFamily,
        pub turns: [TurnValue; 4],
    }

    pub static ITEMS: [ItemRecord; 3] = [
        ItemRecord {
            family: TurnFamily::QuarterTurns,
            turns: [
                TurnValue::Zero,
                TurnValue::One,
                TurnValue::Zero,
                TurnValue::MinusOne,
            ],
        },
        ItemRecord {
            family: TurnFamily::QuarterTurns,
            turns: [
                TurnValue::One,
                TurnValue::Zero,
                TurnValue::MinusOne,
                TurnValue::Zero,
            ],
        },
        ItemRecord {
            family: TurnFamily::Absent,
            turns: [
                TurnValue::Absent,
                TurnValue::Absent,
                TurnValue::Absent,
                TurnValue::Absent,
            ],
        },
    ];

    pub fn items(owner: ItemOwner) -> ItemRecord {
        match owner {
            ItemOwner::Sine => ITEMS[0],
            ItemOwner::Cosine => ITEMS[1],
            ItemOwner::Logarithm => ITEMS[2],
        }
    }

    /// The value at the quarter turn `turn` of the record of `owner`.
    pub fn turn_value(owner: ItemOwner, turn: u8) -> TurnValue {
        let record = items(owner);
        match record.family {
            TurnFamily::Absent => TurnValue::Absent,
            TurnFamily::QuarterTurns => record.turns[(turn % 4) as usize],
        }
    }
}

/// Gauss-Jordan elimination over a field whose zero test answers three ways,
/// in the forms of the crate-private elimination skeleton of the library: a
/// field trait with an element type bounded by `Clone` and `&self` operations
/// that return `Result`; a zero-test subtrait, written with a `where` clause,
/// with an associated reason type and a generic three-valued answer whose
/// unknown answer carries the reason; an uninhabited reason type for fields
/// that always decide, unwrapped by an empty `match`; a storage trait with
/// `&mut self` hooks, one of which receives the pivot list as
/// `&mut Vec<usize>`, and an element equality bound between the two traits.
/// The skeleton has one loop per function: the column loop matches the
/// answer of the pivot search in a tuple and returns a result state from
/// inside the loop, the search returns from inside its loop, and the loop that
/// eliminates from the other rows holds a `?` inside an `if`. The instances
/// are an exact prime field, a prime field whose test answers unknown for one
/// value, a storage that charges, tracks a determinant and releases each
/// completed pivot row in a loop with a `?` inside an `if`, and a storage that
/// reserves its pivot list up front. The names are unique among the
/// qualification modules.
pub mod elimination_skeleton {
    /// The failures of the meter of the skeleton.
    #[derive(Clone, Copy)]
    pub enum PivotFailure {
        Exhausted,
        DivisionByZero,
    }

    pub struct PivotMeter {
        pub left: u64,
    }

    impl PivotMeter {
        pub fn charge(&mut self, amount: u64) -> Result<(), PivotFailure> {
            if amount > self.left {
                return Err(PivotFailure::Exhausted);
            }
            self.left -= amount;
            Ok(())
        }
    }

    /// The answer of a zero test: zero, nonzero, or unknown with a reason.
    pub enum PivotAnswer<U> {
        Zero,
        Nonzero,
        Unknown(U),
    }

    /// The reason type of a field whose zero test always decides.
    pub enum Decided {}

    /// The outcome of a reduction: its pivot columns, or the state that the
    /// zero tests of a column did not decide, with the reason.
    pub enum Elimination<U> {
        Complete(Vec<usize>),
        Undecided(U),
    }

    /// The pivot columns of a reduction over a field that always decides.
    pub fn complete(reduction: Elimination<Decided>) -> Vec<usize> {
        match reduction {
            Elimination::Complete(pivots) => pivots,
            Elimination::Undecided(never) => match never {},
        }
    }

    pub(crate) trait PivotField {
        type Element: Clone;

        fn divide(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            meter: &mut PivotMeter,
        ) -> Result<Self::Element, PivotFailure>;
        fn multiply(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            meter: &mut PivotMeter,
        ) -> Result<Self::Element, PivotFailure>;
        fn subtract(
            &self,
            a: &Self::Element,
            b: &Self::Element,
            meter: &mut PivotMeter,
        ) -> Result<Self::Element, PivotFailure>;
    }

    pub(crate) trait PivotZeroTests
    where
        Self: PivotField,
    {
        type Undecided;

        fn zero_test(
            &self,
            a: &Self::Element,
            meter: &mut PivotMeter,
        ) -> Result<PivotAnswer<Self::Undecided>, PivotFailure>;
    }

    pub(crate) trait PivotRows {
        type Element;

        fn rows(&self) -> usize;
        fn width(&self) -> usize;
        fn entry(&self, row: usize, column: usize) -> &Self::Element;
        fn begin_reduction(
            &mut self,
            variables: usize,
            meter: &mut PivotMeter,
        ) -> Result<Vec<usize>, PivotFailure>;
        fn candidate_step(&self, meter: &mut PivotMeter) -> Result<(), PivotFailure>;
        fn swap_cell(
            &mut self,
            row: usize,
            other: usize,
            column: usize,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure>;
        fn begin_pivot(
            &mut self,
            row: usize,
            column: usize,
            swapped: bool,
            meter: &mut PivotMeter,
        ) -> Result<Self::Element, PivotFailure>;
        fn store(
            &mut self,
            row: usize,
            column: usize,
            value: Self::Element,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure>;
        fn first_target(&self, row: usize) -> usize;
        fn target_step(&self, meter: &mut PivotMeter) -> Result<(), PivotFailure>;
        fn end_pivot(
            &mut self,
            row: usize,
            column: usize,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure>;
        fn reserve_pivot(
            &mut self,
            pivots: &mut Vec<usize>,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure>;
        fn end_reduction(&mut self, meter: &mut PivotMeter) -> Result<(), PivotFailure>;
    }

    pub(crate) fn reduce<F, S>(
        field: &F,
        rows: &mut S,
        variables: usize,
        meter: &mut PivotMeter,
    ) -> Result<Elimination<F::Undecided>, PivotFailure>
    where
        F: PivotZeroTests,
        S: PivotRows<Element = F::Element>,
    {
        let pivots = rows.begin_reduction(variables, meter)?;
        reduce_columns(field, rows, variables, pivots, meter)
    }

    fn reduce_columns<F, S>(
        field: &F,
        rows: &mut S,
        variables: usize,
        pivots: Vec<usize>,
        meter: &mut PivotMeter,
    ) -> Result<Elimination<F::Undecided>, PivotFailure>
    where
        F: PivotZeroTests,
        S: PivotRows<Element = F::Element>,
    {
        let mut pivots = pivots;
        let mut column = 0;
        while column < variables && pivots.len() < rows.rows() {
            let row = pivots.len();
            match find_pivot(field, rows, row, column, meter)? {
                (PivotAnswer::Nonzero, selected) => {
                    pivot_step(field, rows, row, selected, column, &mut pivots, meter)?
                }
                (PivotAnswer::Zero, _) => {}
                (PivotAnswer::Unknown(reason), _) => return Ok(Elimination::Undecided(reason)),
            }
            column += 1;
        }
        rows.end_reduction(meter)?;
        Ok(Elimination::Complete(pivots))
    }

    fn find_pivot<F, S>(
        field: &F,
        rows: &S,
        row: usize,
        column: usize,
        meter: &mut PivotMeter,
    ) -> Result<(PivotAnswer<F::Undecided>, usize), PivotFailure>
    where
        F: PivotZeroTests,
        S: PivotRows<Element = F::Element>,
    {
        let mut answer = PivotAnswer::Zero;
        let mut candidate = row;
        while candidate < rows.rows() {
            rows.candidate_step(meter)?;
            match field.zero_test(rows.entry(candidate, column), meter)? {
                PivotAnswer::Nonzero => return Ok((PivotAnswer::Nonzero, candidate)),
                PivotAnswer::Zero => {}
                PivotAnswer::Unknown(reason) => answer = first_unknown(answer, reason),
            }
            candidate += 1;
        }
        Ok((answer, candidate))
    }

    fn first_unknown<U>(answer: PivotAnswer<U>, reason: U) -> PivotAnswer<U> {
        match answer {
            PivotAnswer::Zero => PivotAnswer::Unknown(reason),
            kept => kept,
        }
    }

    fn pivot_step<F, S>(
        field: &F,
        rows: &mut S,
        row: usize,
        selected: usize,
        column: usize,
        pivots: &mut Vec<usize>,
        meter: &mut PivotMeter,
    ) -> Result<(), PivotFailure>
    where
        F: PivotZeroTests,
        S: PivotRows<Element = F::Element>,
    {
        let swapped = selected != row;
        if swapped {
            swap_rows(rows, row, selected, meter)?;
        }
        let pivot = rows.begin_pivot(row, column, swapped, meter)?;
        normalize_row(field, rows, row, column, &pivot, meter)?;
        eliminate_rows(field, rows, row, column, meter)?;
        rows.end_pivot(row, column, meter)?;
        rows.reserve_pivot(pivots, meter)?;
        pivots.push(column);
        Ok(())
    }

    fn swap_rows<S: PivotRows>(
        rows: &mut S,
        row: usize,
        other: usize,
        meter: &mut PivotMeter,
    ) -> Result<(), PivotFailure> {
        let mut column = 0;
        while column < rows.width() {
            rows.swap_cell(row, other, column, meter)?;
            column += 1;
        }
        Ok(())
    }

    fn normalize_row<F, S>(
        field: &F,
        rows: &mut S,
        row: usize,
        column: usize,
        pivot: &F::Element,
        meter: &mut PivotMeter,
    ) -> Result<(), PivotFailure>
    where
        F: PivotField,
        S: PivotRows<Element = F::Element>,
    {
        let mut c = column;
        while c < rows.width() {
            let value = field.divide(rows.entry(row, c), pivot, meter)?;
            rows.store(row, c, value, meter)?;
            c += 1;
        }
        Ok(())
    }

    fn eliminate_rows<F, S>(
        field: &F,
        rows: &mut S,
        row: usize,
        column: usize,
        meter: &mut PivotMeter,
    ) -> Result<(), PivotFailure>
    where
        F: PivotZeroTests,
        S: PivotRows<Element = F::Element>,
    {
        let mut other = rows.first_target(row);
        while other < rows.rows() {
            rows.target_step(meter)?;
            if other != row {
                eliminate_row(field, rows, row, other, column, meter)?;
            }
            other += 1;
        }
        Ok(())
    }

    fn eliminate_row<F, S>(
        field: &F,
        rows: &mut S,
        row: usize,
        other: usize,
        column: usize,
        meter: &mut PivotMeter,
    ) -> Result<(), PivotFailure>
    where
        F: PivotZeroTests,
        S: PivotRows<Element = F::Element>,
    {
        match field.zero_test(rows.entry(other, column), meter)? {
            PivotAnswer::Zero => Ok(()),
            PivotAnswer::Nonzero | PivotAnswer::Unknown(_) => {
                let factor = rows.entry(other, column).clone();
                subtract_row(field, rows, row, other, column, &factor, meter)
            }
        }
    }

    fn subtract_row<F, S>(
        field: &F,
        rows: &mut S,
        row: usize,
        other: usize,
        column: usize,
        factor: &F::Element,
        meter: &mut PivotMeter,
    ) -> Result<(), PivotFailure>
    where
        F: PivotField,
        S: PivotRows<Element = F::Element>,
    {
        let mut c = column;
        while c < rows.width() {
            let product = field.multiply(factor, rows.entry(row, c), meter)?;
            let value = field.subtract(rows.entry(other, c), &product, meter)?;
            rows.store(other, c, value, meter)?;
            c += 1;
        }
        Ok(())
    }

    /// A prime field with residues as elements, whose inverse is a power.
    #[derive(Clone, Copy)]
    pub struct SkeletonPrime {
        pub p: u32,
    }

    fn residue_product(p: u32, a: u32, b: u32) -> u32 {
        ((u64::from(a) * u64::from(b)) % u64::from(p)) as u32
    }

    fn residue_difference(p: u32, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(p) - u64::from(b)) % u64::from(p)) as u32
    }

    /// `a^(p-2)`, the inverse of a nonzero residue, by binary powering.
    fn residue_inverse(p: u32, a: u32, meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
        if a == 0 {
            return Err(PivotFailure::DivisionByZero);
        }
        let mut base = a;
        let mut n = p - 2;
        let mut result = 1;
        while n != 0 {
            meter.charge(1)?;
            if n & 1 != 0 {
                result = residue_product(p, result, base);
            }
            n >>= 1;
            if n != 0 {
                base = residue_product(p, base, base);
            }
        }
        Ok(result)
    }

    impl PivotField for SkeletonPrime {
        type Element = u32;

        fn divide(&self, a: &u32, b: &u32, meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
            let inverse = residue_inverse(self.p, *b, meter)?;
            meter.charge(1)?;
            Ok(residue_product(self.p, *a, inverse))
        }

        fn multiply(&self, a: &u32, b: &u32, meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
            meter.charge(1)?;
            Ok(residue_product(self.p, *a, *b))
        }

        fn subtract(&self, a: &u32, b: &u32, meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
            meter.charge(1)?;
            Ok(residue_difference(self.p, *a, *b))
        }
    }

    impl PivotZeroTests for SkeletonPrime {
        type Undecided = Decided;

        fn zero_test(
            &self,
            a: &u32,
            _meter: &mut PivotMeter,
        ) -> Result<PivotAnswer<Decided>, PivotFailure> {
            if *a == 0 {
                return Ok(PivotAnswer::Zero);
            }
            Ok(PivotAnswer::Nonzero)
        }
    }

    /// A prime field whose zero test charges and answers unknown for one
    /// value, as a field with an undecidable test would.
    #[derive(Clone, Copy)]
    pub struct HazyPrime {
        pub p: u32,
        pub hazy: u32,
    }

    impl PivotField for HazyPrime {
        type Element = u32;

        fn divide(&self, a: &u32, b: &u32, meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
            let inverse = residue_inverse(self.p, *b, meter)?;
            Ok(residue_product(self.p, *a, inverse))
        }

        fn multiply(&self, a: &u32, b: &u32, _meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
            Ok(residue_product(self.p, *a, *b))
        }

        fn subtract(&self, a: &u32, b: &u32, _meter: &mut PivotMeter) -> Result<u32, PivotFailure> {
            Ok(residue_difference(self.p, *a, *b))
        }
    }

    impl PivotZeroTests for HazyPrime {
        type Undecided = ();

        fn zero_test(
            &self,
            a: &u32,
            meter: &mut PivotMeter,
        ) -> Result<PivotAnswer<()>, PivotFailure> {
            meter.charge(1)?;
            if *a == self.hazy {
                return Ok(PivotAnswer::Unknown(()));
            }
            if *a == 0 {
                return Ok(PivotAnswer::Zero);
            }
            Ok(PivotAnswer::Nonzero)
        }
    }

    /// Rows that charge each candidate, swap, pivot, target and pivot column,
    /// optionally track the determinant, eliminating only below each pivot
    /// and releasing each completed pivot row, and bound each stored entry.
    pub struct ChargedRows {
        pub rows: usize,
        pub columns: usize,
        pub entries: Vec<u32>,
        pub p: u32,
        pub cap: u32,
        pub track: bool,
        pub determinant: u32,
    }

    impl ChargedRows {
        fn put(
            &mut self,
            index: usize,
            value: u32,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            meter.charge(1)?;
            if value > self.cap {
                return Err(PivotFailure::Exhausted);
            }
            self.entries[index] = value;
            Ok(())
        }

        fn release_row(
            &mut self,
            row: usize,
            column: usize,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            let mut c = column;
            while c < self.columns {
                let index = row * self.columns + c;
                if self.entries[index] != 0 {
                    self.put(index, 0, meter)?;
                }
                c += 1;
            }
            Ok(())
        }
    }

    impl PivotRows for ChargedRows {
        type Element = u32;

        fn rows(&self) -> usize {
            self.rows
        }

        fn width(&self) -> usize {
            self.columns
        }

        fn entry(&self, row: usize, column: usize) -> &u32 {
            &self.entries[row * self.columns + column]
        }

        fn begin_reduction(
            &mut self,
            _variables: usize,
            _meter: &mut PivotMeter,
        ) -> Result<Vec<usize>, PivotFailure> {
            Ok(Vec::new())
        }

        fn candidate_step(&self, meter: &mut PivotMeter) -> Result<(), PivotFailure> {
            meter.charge(1)
        }

        fn swap_cell(
            &mut self,
            row: usize,
            other: usize,
            column: usize,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            meter.charge(1)?;
            self.entries
                .swap(row * self.columns + column, other * self.columns + column);
            Ok(())
        }

        fn begin_pivot(
            &mut self,
            row: usize,
            column: usize,
            swapped: bool,
            meter: &mut PivotMeter,
        ) -> Result<u32, PivotFailure> {
            if swapped && self.track {
                self.determinant = residue_difference(self.p, 0, self.determinant);
            }
            meter.charge(1)?;
            let pivot = self.entries[row * self.columns + column];
            if self.track {
                self.determinant = residue_product(self.p, self.determinant, pivot);
            }
            Ok(pivot)
        }

        fn store(
            &mut self,
            row: usize,
            column: usize,
            value: u32,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            self.put(row * self.columns + column, value, meter)
        }

        fn first_target(&self, row: usize) -> usize {
            if self.track { row + 1 } else { 0 }
        }

        fn target_step(&self, meter: &mut PivotMeter) -> Result<(), PivotFailure> {
            meter.charge(1)
        }

        fn end_pivot(
            &mut self,
            row: usize,
            column: usize,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            if self.track && row + 1 < self.rows {
                self.release_row(row, column, meter)?;
            }
            Ok(())
        }

        fn reserve_pivot(
            &mut self,
            _pivots: &mut Vec<usize>,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            meter.charge(1)
        }

        fn end_reduction(&mut self, meter: &mut PivotMeter) -> Result<(), PivotFailure> {
            meter.charge(0)
        }
    }

    /// Rows that reserve the pivot list up front and otherwise charge
    /// nothing of their own.
    pub struct FreeRows {
        pub rows: usize,
        pub columns: usize,
        pub entries: Vec<u32>,
    }

    impl PivotRows for FreeRows {
        type Element = u32;

        fn rows(&self) -> usize {
            self.rows
        }

        fn width(&self) -> usize {
            self.columns
        }

        fn entry(&self, row: usize, column: usize) -> &u32 {
            &self.entries[row * self.columns + column]
        }

        fn begin_reduction(
            &mut self,
            variables: usize,
            meter: &mut PivotMeter,
        ) -> Result<Vec<usize>, PivotFailure> {
            let count = if variables < self.rows {
                variables
            } else {
                self.rows
            };
            meter.charge(count as u64)?;
            Ok(Vec::with_capacity(count))
        }

        fn candidate_step(&self, _meter: &mut PivotMeter) -> Result<(), PivotFailure> {
            Ok(())
        }

        fn swap_cell(
            &mut self,
            row: usize,
            other: usize,
            column: usize,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            meter.charge(1)?;
            self.entries
                .swap(row * self.columns + column, other * self.columns + column);
            Ok(())
        }

        fn begin_pivot(
            &mut self,
            row: usize,
            column: usize,
            _swapped: bool,
            _meter: &mut PivotMeter,
        ) -> Result<u32, PivotFailure> {
            Ok(self.entries[row * self.columns + column])
        }

        fn store(
            &mut self,
            row: usize,
            column: usize,
            value: u32,
            meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            meter.charge(1)?;
            self.entries[row * self.columns + column] = value;
            Ok(())
        }

        fn first_target(&self, _row: usize) -> usize {
            0
        }

        fn target_step(&self, _meter: &mut PivotMeter) -> Result<(), PivotFailure> {
            Ok(())
        }

        fn end_pivot(
            &mut self,
            _row: usize,
            _column: usize,
            _meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            Ok(())
        }

        fn reserve_pivot(
            &mut self,
            _pivots: &mut Vec<usize>,
            _meter: &mut PivotMeter,
        ) -> Result<(), PivotFailure> {
            Ok(())
        }

        fn end_reduction(&mut self, _meter: &mut PivotMeter) -> Result<(), PivotFailure> {
            Ok(())
        }
    }

    /// The pivot columns of `entries` over the exact prime field, with
    /// charged rows that do not track the determinant.
    pub fn pivots_prime(
        p: u32,
        rows: usize,
        columns: usize,
        entries: Vec<u32>,
        meter: &mut PivotMeter,
    ) -> Result<Vec<usize>, PivotFailure> {
        let field = SkeletonPrime { p };
        let mut storage = ChargedRows {
            rows,
            columns,
            entries,
            p,
            cap: p,
            track: false,
            determinant: 1,
        };
        let reduction = reduce(&field, &mut storage, columns, meter)?;
        Ok(complete(reduction))
    }

    /// The determinant of a square matrix over the exact prime field, with
    /// charged rows that track it.
    pub fn determinant_prime(
        p: u32,
        n: usize,
        entries: Vec<u32>,
        meter: &mut PivotMeter,
    ) -> Result<u32, PivotFailure> {
        let field = SkeletonPrime { p };
        let mut storage = ChargedRows {
            rows: n,
            columns: n,
            entries,
            p,
            cap: p,
            track: true,
            determinant: 1,
        };
        let reduction = reduce(&field, &mut storage, n, meter)?;
        let pivots = complete(reduction);
        if pivots.len() == n {
            return Ok(storage.determinant);
        }
        Ok(0)
    }

    /// The reduction of `entries` over the prime field that answers unknown
    /// for `hazy`, with free rows: a result state when a column is
    /// undecided.
    pub fn reduce_hazy(
        p: u32,
        hazy: u32,
        rows: usize,
        columns: usize,
        entries: Vec<u32>,
        meter: &mut PivotMeter,
    ) -> Result<Elimination<()>, PivotFailure> {
        let field = HazyPrime { p, hazy };
        let mut storage = FreeRows {
            rows,
            columns,
            entries,
        };
        reduce(&field, &mut storage, columns, meter)
    }
}

/// A generic helper with one loop, bounded by a subtrait that has an
/// associated type of its own, whose loop calls only methods of the
/// supertrait, next to a storage trait with an element equality bound. The
/// loop does not use the subtrait's associated type, and Aeneas loses it in
/// the loop's signature. The elimination skeleton bounds such helpers by the
/// supertrait.
pub mod subtrait_loop {
    use crate::budget::{Budget, Exhausted};

    pub(crate) trait LoopUnits {
        type Unit: Clone;

        fn double(&self, a: &Self::Unit, budget: &mut Budget) -> Result<Self::Unit, Exhausted>;
    }

    pub(crate) trait LoopTags
    where
        Self: LoopUnits,
    {
        type Tag;

        fn tag(&self, a: &Self::Unit, budget: &mut Budget) -> Result<Self::Tag, Exhausted>;
    }

    pub(crate) trait LoopCells {
        type Cell;

        fn length(&self) -> usize;
        fn cell(&self, index: usize) -> &Self::Cell;
        fn put(&mut self, index: usize, value: Self::Cell);
    }

    /// Doubles every cell: the loop calls only the supertrait.
    fn double_cells<F, S>(field: &F, cells: &mut S, budget: &mut Budget) -> Result<(), Exhausted>
    where
        F: LoopTags,
        S: LoopCells<Cell = F::Unit>,
    {
        let mut index = 0;
        while index < cells.length() {
            let value = field.double(cells.cell(index), budget)?;
            cells.put(index, value);
            index += 1;
        }
        Ok(())
    }

    pub struct Words;

    impl LoopUnits for Words {
        type Unit = u32;

        fn double(&self, a: &u32, budget: &mut Budget) -> Result<u32, Exhausted> {
            budget.take(1)?;
            Ok(a.wrapping_mul(2))
        }
    }

    impl LoopTags for Words {
        type Tag = bool;

        fn tag(&self, a: &u32, budget: &mut Budget) -> Result<bool, Exhausted> {
            budget.take(1)?;
            Ok(*a == 0)
        }
    }

    pub struct WordCells {
        pub values: Vec<u32>,
    }

    impl LoopCells for WordCells {
        type Cell = u32;

        fn length(&self) -> usize {
            self.values.len()
        }

        fn cell(&self, index: usize) -> &u32 {
            &self.values[index]
        }

        fn put(&mut self, index: usize, value: u32) {
            self.values[index] = value;
        }
    }

    /// The first value doubled and tagged.
    pub fn double_and_tag(values: Vec<u32>, budget: &mut Budget) -> Result<bool, Exhausted> {
        let mut cells = WordCells { values };
        double_cells(&Words, &mut cells, budget)?;
        Words.tag(cells.cell(0), budget)
    }
}

/// Function-expression terms in the former layout of the library: a node with
/// a cached node count whose kind holds its children as shared pointers, the
/// operands of sums and products as vectors of them and a call head that
/// carries a root degree. The walks over a term are loops over explicit
/// stacks held in vectors that are overwritten by index and never popped: the
/// positions in pre-order, and structural equality, which compares pairs of
/// nodes and pushes the pairs of their children in a helper with its own loop.
///
/// The generated code does not type-check: `Arc` is an external type, and the
/// kernel rejects the recursive kind whose children occur inside it. With
/// `Arc<T>` defined as a structure with one field of type `T`, `deref`
/// returning the field and `clone` the same value, it does.
pub mod shared_term {
    use crate::budget::{Budget, Exhausted};
    use std::sync::Arc;

    #[derive(Clone, Copy)]
    pub enum TermHead {
        Sine,
        Root(u32),
    }

    pub enum TermKind {
        Number(i64),
        Symbol(u32),
        Sum(Vec<Term>),
        Product(Vec<Term>),
        Power(Term, Term),
        Call(TermHead, Term),
        Opaque(u32),
    }

    pub struct TermNode {
        pub kind: TermKind,
        pub nodes: usize,
    }

    pub type Term = Arc<TermNode>;

    /// The number of children of a node: the operands of a sum or product,
    /// the base and exponent of a power, the argument of a call; an opaque
    /// node has none.
    pub fn children(term: &Term) -> usize {
        match &term.kind {
            TermKind::Sum(operands) => operands.len(),
            TermKind::Product(operands) => operands.len(),
            TermKind::Power(_, _) => 2,
            TermKind::Call(_, _) => 1,
            TermKind::Number(_) => 0,
            TermKind::Symbol(_) => 0,
            TermKind::Opaque(_) => 0,
        }
    }

    /// Child `index` of a node, shared; a node without children returns
    /// itself.
    pub fn child(term: &Term, index: usize) -> Term {
        match &term.kind {
            TermKind::Sum(operands) => Arc::clone(&operands[index]),
            TermKind::Product(operands) => Arc::clone(&operands[index]),
            TermKind::Power(base, exponent) => {
                if index == 0 {
                    Arc::clone(base)
                } else {
                    Arc::clone(exponent)
                }
            }
            TermKind::Call(_, argument) => Arc::clone(argument),
            TermKind::Number(_) => Arc::clone(term),
            TermKind::Symbol(_) => Arc::clone(term),
            TermKind::Opaque(_) => Arc::clone(term),
        }
    }

    pub struct WalkFrame {
        pub term: Term,
        pub next: usize,
    }

    fn put_frame(stack: &mut Vec<WalkFrame>, index: usize, frame: WalkFrame) {
        if index < stack.len() {
            stack[index] = frame;
        } else {
            stack.push(frame);
        }
    }

    /// The number of positions of `term`, visited in pre-order by one loop
    /// that charges before every step.
    pub fn positions(term: &Term, budget: &mut Budget) -> Result<usize, Exhausted> {
        let mut stack = Vec::new();
        stack.push(WalkFrame {
            term: Arc::clone(term),
            next: 0,
        });
        let mut depth = 1;
        let mut visited = 0;
        while depth > 0 {
            budget.take(1)?;
            let top = depth - 1;
            if stack[top].next == 0 {
                visited += 1;
            }
            if stack[top].next < children(&stack[top].term) {
                let next = child(&stack[top].term, stack[top].next);
                stack[top].next += 1;
                put_frame(
                    &mut stack,
                    depth,
                    WalkFrame {
                        term: next,
                        next: 0,
                    },
                );
                depth += 1;
            } else {
                depth -= 1;
            }
        }
        Ok(visited)
    }

    /// Whether two nodes agree in kind, literal, head and number of children.
    fn same_node(a: &Term, b: &Term) -> bool {
        match &a.kind {
            TermKind::Number(x) => match &b.kind {
                TermKind::Number(y) => *x == *y,
                _ => false,
            },
            TermKind::Symbol(x) => match &b.kind {
                TermKind::Symbol(y) => *x == *y,
                _ => false,
            },
            TermKind::Opaque(x) => match &b.kind {
                TermKind::Opaque(y) => *x == *y,
                _ => false,
            },
            TermKind::Sum(x) => match &b.kind {
                TermKind::Sum(y) => x.len() == y.len(),
                _ => false,
            },
            TermKind::Product(x) => match &b.kind {
                TermKind::Product(y) => x.len() == y.len(),
                _ => false,
            },
            TermKind::Power(_, _) => matches!(&b.kind, TermKind::Power(_, _)),
            TermKind::Call(f, _) => match &b.kind {
                TermKind::Call(g, _) => same_head(*f, *g),
                _ => false,
            },
        }
    }

    pub fn same_head(a: TermHead, b: TermHead) -> bool {
        match a {
            TermHead::Sine => match b {
                TermHead::Sine => true,
                TermHead::Root(_) => false,
            },
            TermHead::Root(m) => match b {
                TermHead::Sine => false,
                TermHead::Root(n) => m == n,
            },
        }
    }

    pub struct TermPair {
        pub left: Term,
        pub right: Term,
    }

    fn put_pair(stack: &mut Vec<TermPair>, index: usize, pair: TermPair) {
        if index < stack.len() {
            stack[index] = pair;
        } else {
            stack.push(pair);
        }
    }

    /// Pushes the pairs of the children of two nodes that agree, from
    /// `depth` on, and returns the new depth.
    fn push_children(stack: &mut Vec<TermPair>, depth: usize, a: &Term, b: &Term) -> usize {
        let count = children(a);
        let mut top = depth;
        let mut index = 0;
        while index < count {
            put_pair(
                stack,
                top,
                TermPair {
                    left: child(a, index),
                    right: child(b, index),
                },
            );
            top += 1;
            index += 1;
        }
        top
    }

    /// Structural equality, charged before every pair of nodes.
    pub fn same(a: &Term, b: &Term, budget: &mut Budget) -> Result<bool, Exhausted> {
        let mut stack = Vec::new();
        stack.push(TermPair {
            left: Arc::clone(a),
            right: Arc::clone(b),
        });
        let mut depth = 1;
        while depth > 0 {
            budget.take(1)?;
            depth -= 1;
            let left = Arc::clone(&stack[depth].left);
            let right = Arc::clone(&stack[depth].right);
            if !same_node(&left, &right) {
                return Ok(false);
            }
            depth = push_children(&mut stack, depth, &left, &right);
        }
        Ok(true)
    }
}

/// The term layout of function expressions with the parts that `shared_term`
/// leaves out: a kind that holds the bindings of a formal substitution, a
/// `BTreeMap` from names to terms, inside a type of its own; a payload type of
/// opaque nodes held in a `Box`; and a guard type that terms hold and that
/// holds terms and guards, mutually recursive with the terms through `Arc` and
/// `Vec`, as the conditions of piecewise terms are. The case cuts the bindings
/// and payload types through its `opaque` field and installs reviewed external
/// declarations in which `Arc` is a structure: with both, the generated code
/// type-checks, while terms held in the map itself do not
/// (`collection-tree-map`). A walk counts the positions of a term in one loop
/// over an explicit stack, charging before every step, without entering
/// opaque nodes, guards or bindings.
pub mod term_layout_cut {
    use crate::budget::{Budget, Exhausted};
    use std::collections::BTreeMap;
    use std::sync::Arc;

    pub type LayoutTerm = Arc<LayoutNode>;
    pub type LayoutGuard = Arc<LayoutCondition>;

    /// The bindings of a formal substitution, by variable name.
    pub struct LayoutBindings(pub BTreeMap<String, LayoutTerm>);

    /// The payload of an opaque node.
    pub struct LayoutPayload {
        pub digits: Vec<u8>,
    }

    pub enum LayoutKind {
        Number(i64),
        Symbol(String),
        Sum(Vec<LayoutTerm>),
        Power(LayoutTerm, LayoutTerm),
        Call(u32, LayoutTerm),
        Algebraic(Box<LayoutPayload>),
        Piecewise(LayoutGuard, LayoutTerm, LayoutTerm),
        Substitute(LayoutTerm, LayoutBindings),
    }

    pub struct LayoutNode {
        pub kind: LayoutKind,
        pub nodes: usize,
    }

    pub enum LayoutConditionKind {
        Bool(bool),
        Compare(LayoutTerm, LayoutTerm),
        Stable(LayoutGuard, String),
        Not(LayoutGuard),
        And(Vec<LayoutGuard>),
    }

    pub struct LayoutCondition {
        pub kind: LayoutConditionKind,
        pub nodes: usize,
    }

    /// The number of children that the walk visits: the operands of a sum, the
    /// base and exponent of a power and the argument of a call. Opaque nodes,
    /// piecewise terms and substitutions have none.
    pub fn layout_children(term: &LayoutTerm) -> usize {
        match &term.kind {
            LayoutKind::Sum(operands) => operands.len(),
            LayoutKind::Power(_, _) => 2,
            LayoutKind::Call(_, _) => 1,
            _ => 0,
        }
    }

    /// Child `index` of a node, shared; a node without children returns
    /// itself.
    pub fn layout_child(term: &LayoutTerm, index: usize) -> LayoutTerm {
        match &term.kind {
            LayoutKind::Sum(operands) => Arc::clone(&operands[index]),
            LayoutKind::Power(base, exponent) => {
                if index == 0 {
                    Arc::clone(base)
                } else {
                    Arc::clone(exponent)
                }
            }
            LayoutKind::Call(_, argument) => Arc::clone(argument),
            _ => Arc::clone(term),
        }
    }

    pub struct LayoutFrame {
        pub term: LayoutTerm,
        pub next: usize,
    }

    fn put_layout_frame(stack: &mut Vec<LayoutFrame>, index: usize, frame: LayoutFrame) {
        if index < stack.len() {
            stack[index] = frame;
        } else {
            stack.push(frame);
        }
    }

    /// The number of positions of `term`, visited in pre-order by one loop
    /// that charges before every step.
    pub fn layout_positions(term: &LayoutTerm, budget: &mut Budget) -> Result<usize, Exhausted> {
        let mut stack = Vec::new();
        stack.push(LayoutFrame {
            term: Arc::clone(term),
            next: 0,
        });
        let mut depth = 1;
        let mut visited = 0;
        while depth > 0 {
            budget.take(1)?;
            let top = depth - 1;
            if stack[top].next == 0 {
                visited += 1;
            }
            if stack[top].next < layout_children(&stack[top].term) {
                let next = layout_child(&stack[top].term, stack[top].next);
                stack[top].next += 1;
                put_layout_frame(
                    &mut stack,
                    depth,
                    LayoutFrame {
                        term: next,
                        next: 0,
                    },
                );
                depth += 1;
            } else {
                depth -= 1;
            }
        }
        Ok(visited)
    }

    /// Whether a term is a substitution, read through its kind without
    /// entering the bindings.
    pub fn is_substitution(term: &LayoutTerm) -> bool {
        matches!(term.kind, LayoutKind::Substitute(_, _))
    }

    /// Whether a guard is a negation, read through its kind.
    pub fn is_negation(guard: &LayoutGuard) -> bool {
        matches!(guard.kind, LayoutConditionKind::Not(_))
    }
}

/// A matcher in the form the rewrite engine uses, over the terms of
/// `shared_term`: a pattern stored as a vector of copyable nodes that refer to
/// their children by index; a machine whose goal, trail and choice stacks are
/// vectors overwritten by index; one loop that charges before every step,
/// binds a wildcard to a shared copy of a subterm or compares a repeated one
/// by structural equality, matches the operands of a sum pattern to the
/// operands of a subject sum in any order through choice points, reports every
/// complete match to a consumer, a generic parameter bounded by a crate-private
/// trait, and returns from inside the loop when the consumer stops it; and
/// backtracking in a helper whose loop undoes bindings and tries the next
/// operand in helpers with loops of their own. No function is recursive. A
/// sum assigned to a field of a choice point is computed into a local first
/// (`indexed_field_sum`).
///
/// Like `shared_term`, whose terms it matches, the generated code type-checks
/// only with `Arc` defined as a structure.
pub mod match_machine {
    use crate::budget::{Budget, Exhausted};
    use crate::shared_term::{Term, TermHead, TermKind, child, children, same, same_head};
    use std::sync::Arc;

    #[derive(Clone, Copy)]
    pub enum PatternNode {
        Number(i64),
        Symbol(u32),
        Wild(usize),
        Call(TermHead, usize),
        /// A sum whose operand patterns are `operands[start..start + count]`.
        Sum(usize, usize),
    }

    pub struct FlatPattern {
        pub nodes: Vec<PatternNode>,
        pub operands: Vec<usize>,
        pub wildcards: usize,
    }

    pub enum Goal {
        /// Match pattern node `.0` against `.1`.
        Match(usize, Term),
        /// Assign operand `.1` of the sum pattern node `.0` to an operand of
        /// the subject sum `.2` that the mask `.3` has not taken.
        Assign(usize, usize, Term, u64),
    }

    pub struct Choice {
        pub goals: usize,
        pub trail: usize,
        pub sum: usize,
        pub next: usize,
        pub term: Term,
        pub used: u64,
        pub candidate: usize,
    }

    #[derive(Clone, Copy)]
    pub enum MatchFlow {
        Continue,
        Stop,
    }

    pub(crate) trait MatchConsumer {
        fn found(
            &mut self,
            slots: &[Option<Term>],
            budget: &mut Budget,
        ) -> Result<MatchFlow, Exhausted>;
    }

    pub struct Machine {
        pub goals: Vec<Goal>,
        pub goal_len: usize,
        pub trail: Vec<usize>,
        pub trail_len: usize,
        pub choices: Vec<Choice>,
        pub choice_len: usize,
        pub slots: Vec<Option<Term>>,
    }

    fn copy_goal(goal: &Goal) -> Goal {
        match goal {
            Goal::Match(pattern, term) => Goal::Match(*pattern, Arc::clone(term)),
            Goal::Assign(sum, next, term, used) => {
                Goal::Assign(*sum, *next, Arc::clone(term), *used)
            }
        }
    }

    fn put_goal(goals: &mut Vec<Goal>, index: usize, goal: Goal) {
        if index < goals.len() {
            goals[index] = goal;
        } else {
            goals.push(goal);
        }
    }

    fn put_index(values: &mut Vec<usize>, index: usize, value: usize) {
        if index < values.len() {
            values[index] = value;
        } else {
            values.push(value);
        }
    }

    fn put_choice(choices: &mut Vec<Choice>, index: usize, choice: Choice) {
        if index < choices.len() {
            choices[index] = choice;
        } else {
            choices.push(choice);
        }
    }

    fn empty_slots(count: usize) -> Vec<Option<Term>> {
        let mut slots = Vec::new();
        let mut index = 0;
        while index < count {
            slots.push(None);
            index += 1;
        }
        slots
    }

    /// The first operand of the subject at or after `from` that `used` has
    /// not taken, or `count` if there is none.
    fn next_free(used: u64, from: usize, count: usize) -> usize {
        let mut index = from;
        while index < count {
            if (used >> index) & 1 == 0 {
                return index;
            }
            index += 1;
        }
        count
    }

    impl Machine {
        fn new(wildcards: usize, subject: &Term) -> Machine {
            let mut goals = Vec::new();
            put_goal(&mut goals, 0, Goal::Match(0, Arc::clone(subject)));
            Machine {
                goals,
                goal_len: 1,
                trail: Vec::new(),
                trail_len: 0,
                choices: Vec::new(),
                choice_len: 0,
                slots: empty_slots(wildcards),
            }
        }

        fn push_goal(&mut self, goal: Goal) {
            put_goal(&mut self.goals, self.goal_len, goal);
            self.goal_len += 1;
        }

        /// Removes the bindings made after the trail had `length` entries.
        fn undo(&mut self, length: usize) {
            while self.trail_len > length {
                self.trail_len -= 1;
                let slot = self.trail[self.trail_len];
                self.slots[slot] = None;
            }
        }

        /// Matches a pattern node against a term, pushing subgoals.
        fn match_goal(
            &mut self,
            pattern: &FlatPattern,
            node: usize,
            term: Term,
            budget: &mut Budget,
        ) -> Result<bool, Exhausted> {
            match pattern.nodes[node] {
                PatternNode::Number(value) => match &term.kind {
                    TermKind::Number(x) => Ok(*x == value),
                    _ => Ok(false),
                },
                PatternNode::Symbol(name) => match &term.kind {
                    TermKind::Symbol(x) => Ok(*x == name),
                    _ => Ok(false),
                },
                PatternNode::Wild(slot) => {
                    if let Some(bound) = &self.slots[slot] {
                        return same(bound, &term, budget);
                    }
                    self.slots[slot] = Some(term);
                    put_index(&mut self.trail, self.trail_len, slot);
                    self.trail_len += 1;
                    Ok(true)
                }
                PatternNode::Call(head, argument) => match &term.kind {
                    TermKind::Call(h, a) => {
                        if !same_head(head, *h) {
                            return Ok(false);
                        }
                        let a = Arc::clone(a);
                        self.push_goal(Goal::Match(argument, a));
                        Ok(true)
                    }
                    _ => Ok(false),
                },
                PatternNode::Sum(_, count) => match &term.kind {
                    TermKind::Sum(operands) => {
                        if operands.len() != count || count > 64 {
                            return Ok(false);
                        }
                        let subject = Arc::clone(&term);
                        self.push_goal(Goal::Assign(node, 0, subject, 0));
                        Ok(true)
                    }
                    _ => Ok(false),
                },
            }
        }

        /// Processes the top goal; `false` means that it failed or that it
        /// opened a choice point, which backtracking enters.
        fn step(&mut self, pattern: &FlatPattern, budget: &mut Budget) -> Result<bool, Exhausted> {
            self.goal_len -= 1;
            let goal = copy_goal(&self.goals[self.goal_len]);
            match goal {
                Goal::Match(node, term) => self.match_goal(pattern, node, term, budget),
                Goal::Assign(sum, next, term, used) => {
                    let count = children(&term);
                    if next == count {
                        return Ok(true);
                    }
                    let choice = Choice {
                        goals: self.goal_len,
                        trail: self.trail_len,
                        sum,
                        next,
                        term,
                        used,
                        candidate: 0,
                    };
                    put_choice(&mut self.choices, self.choice_len, choice);
                    self.choice_len += 1;
                    Ok(false)
                }
            }
        }

        /// Resumes the newest choice point with an alternative; `false` when
        /// no choice point has one left.
        fn backtrack(
            &mut self,
            pattern: &FlatPattern,
            budget: &mut Budget,
        ) -> Result<bool, Exhausted> {
            while self.choice_len > 0 {
                budget.take(1)?;
                let top = self.choice_len - 1;
                let length = self.choices[top].trail;
                self.undo(length);
                self.goal_len = self.choices[top].goals;
                let count = children(&self.choices[top].term);
                let used = self.choices[top].used;
                let index = next_free(used, self.choices[top].candidate, count);
                if index < count {
                    let candidate = index + 1;
                    self.choices[top].candidate = candidate;
                    let sum = self.choices[top].sum;
                    let next = self.choices[top].next;
                    let term = Arc::clone(&self.choices[top].term);
                    let operand = child(&term, index);
                    let start = match pattern.nodes[sum] {
                        PatternNode::Sum(start, _) => start,
                        _ => 0,
                    };
                    let node = pattern.operands[start + next];
                    self.push_goal(Goal::Assign(sum, next + 1, term, used | (1 << index)));
                    self.push_goal(Goal::Match(node, operand));
                    return Ok(true);
                }
                self.choice_len -= 1;
            }
            Ok(false)
        }
    }

    /// Reports every match of `pattern` against `subject`, in the order of
    /// the search, until the consumer stops.
    pub(crate) fn run<C: MatchConsumer>(
        pattern: &FlatPattern,
        subject: &Term,
        consumer: &mut C,
        budget: &mut Budget,
    ) -> Result<MatchFlow, Exhausted> {
        let mut machine = Machine::new(pattern.wildcards, subject);
        loop {
            budget.take(1)?;
            let advanced = if machine.goal_len == 0 {
                match consumer.found(&machine.slots, budget)? {
                    MatchFlow::Stop => return Ok(MatchFlow::Stop),
                    MatchFlow::Continue => {}
                }
                false
            } else {
                machine.step(pattern, budget)?
            };
            if !advanced && !machine.backtrack(pattern, budget)? {
                return Ok(MatchFlow::Continue);
            }
        }
    }

    /// Counts matches up to a limit.
    pub struct CountMatches {
        pub found: usize,
        pub limit: usize,
    }

    impl MatchConsumer for CountMatches {
        fn found(
            &mut self,
            _slots: &[Option<Term>],
            budget: &mut Budget,
        ) -> Result<MatchFlow, Exhausted> {
            budget.take(1)?;
            self.found += 1;
            if self.found < self.limit {
                Ok(MatchFlow::Continue)
            } else {
                Ok(MatchFlow::Stop)
            }
        }
    }

    /// The number of matches of `pattern` against `subject`, at most
    /// `limit`.
    pub fn count_matches(
        pattern: &FlatPattern,
        subject: &Term,
        limit: usize,
        budget: &mut Budget,
    ) -> Result<usize, Exhausted> {
        let mut consumer = CountMatches { found: 0, limit };
        run(pattern, subject, &mut consumer, budget)?;
        Ok(consumer.found)
    }
}

/// The choice points of matching up to commutativity and associativity: the
/// injective assignments of the fixed operands of a sum pattern to the
/// operands of a subject, enumerated in lexicographic order by one
/// backtracking loop over a vector of chosen indices, with no recursion and no
/// `pop`; each complete assignment is reported to a consumer, a generic
/// parameter bounded by a crate-private trait whose `&mut self` method decides
/// whether the search goes on, and the search returns from inside its loop
/// when the consumer stops it. One consumer collects the assignments up to a
/// limit, another stops at the first assignment that passes a test.
pub mod match_search {
    use crate::budget::{Budget, Exhausted};

    #[derive(Clone, Copy)]
    pub enum SearchFlow {
        Continue,
        Stop,
    }

    pub(crate) trait Consumer {
        fn accept(
            &mut self,
            choice: &[usize],
            budget: &mut Budget,
        ) -> Result<SearchFlow, Exhausted>;
    }

    /// Whether `candidate` is among the first `depth` chosen indices.
    fn taken(choice: &[usize], depth: usize, candidate: usize) -> bool {
        let mut index = 0;
        while index < depth {
            if choice[index] == candidate {
                return true;
            }
            index += 1;
        }
        false
    }

    /// Reports every injective map from the slots of `choice` to
    /// `0..operands`, in lexicographic order, until the consumer stops.
    pub(crate) fn search<C: Consumer>(
        choice: &mut [usize],
        operands: usize,
        consumer: &mut C,
        budget: &mut Budget,
    ) -> Result<SearchFlow, Exhausted> {
        let fixed = choice.len();
        let mut depth = 0;
        let mut candidate = 0;
        loop {
            budget.take(1)?;
            if depth == fixed {
                match consumer.accept(choice, budget)? {
                    SearchFlow::Stop => return Ok(SearchFlow::Stop),
                    SearchFlow::Continue => {}
                }
                if depth == 0 {
                    return Ok(SearchFlow::Continue);
                }
                depth -= 1;
                candidate = choice[depth] + 1;
            } else if candidate == operands {
                if depth == 0 {
                    return Ok(SearchFlow::Continue);
                }
                depth -= 1;
                candidate = choice[depth] + 1;
            } else if taken(choice, depth, candidate) {
                candidate += 1;
            } else {
                choice[depth] = candidate;
                depth += 1;
                candidate = 0;
            }
        }
    }

    fn copy(choice: &[usize]) -> Vec<usize> {
        let mut result = Vec::new();
        let mut index = 0;
        while index < choice.len() {
            result.push(choice[index]);
            index += 1;
        }
        result
    }

    /// Collects assignments until `limit` of them are found.
    pub struct Collect {
        pub found: Vec<Vec<usize>>,
        pub limit: usize,
    }

    impl Consumer for Collect {
        fn accept(
            &mut self,
            choice: &[usize],
            budget: &mut Budget,
        ) -> Result<SearchFlow, Exhausted> {
            budget.take(1)?;
            self.found.push(copy(choice));
            if self.found.len() < self.limit {
                Ok(SearchFlow::Continue)
            } else {
                Ok(SearchFlow::Stop)
            }
        }
    }

    fn total(choice: &[usize]) -> usize {
        let mut sum = 0;
        let mut index = 0;
        while index < choice.len() {
            sum += choice[index];
            index += 1;
        }
        sum
    }

    /// Stops at the first assignment whose indices add up to `wanted`.
    pub struct FirstWith {
        pub wanted: usize,
        pub hit: bool,
    }

    impl Consumer for FirstWith {
        fn accept(
            &mut self,
            choice: &[usize],
            budget: &mut Budget,
        ) -> Result<SearchFlow, Exhausted> {
            budget.take(1)?;
            if total(choice) == self.wanted {
                self.hit = true;
                return Ok(SearchFlow::Stop);
            }
            Ok(SearchFlow::Continue)
        }
    }

    fn slots(count: usize) -> Vec<usize> {
        let mut result = Vec::new();
        let mut index = 0;
        while index < count {
            result.push(0);
            index += 1;
        }
        result
    }

    /// The first `limit` assignments of `fixed` operands to `operands`.
    pub fn collect(
        fixed: usize,
        operands: usize,
        limit: usize,
        budget: &mut Budget,
    ) -> Result<Vec<Vec<usize>>, Exhausted> {
        let mut choice = slots(fixed);
        let mut consumer = Collect {
            found: Vec::new(),
            limit,
        };
        search(&mut choice, operands, &mut consumer, budget)?;
        Ok(consumer.found)
    }

    /// Whether some assignment adds up to `wanted`.
    pub fn first_with(
        fixed: usize,
        operands: usize,
        wanted: usize,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        let mut choice = slots(fixed);
        let mut consumer = FirstWith { wanted, hit: false };
        search(&mut choice, operands, &mut consumer, budget)?;
        Ok(consumer.hit)
    }
}

/// Strategies in the form the rewrite engine uses: a strategy stored as a
/// vector of copyable nodes that refer to their components by index, and an
/// interpreter that is one loop over an explicit stack of copyable frames,
/// with no recursion: a sequence applies its components in order, an
/// alternative stops at the first component that fires, and a bounded
/// repetition applies its component until it fires nothing or reaches its
/// cap, which is a result state. A trace vector is extended by every firing
/// and reaches the caller only with a result.
pub mod strategy_data {
    use crate::budget::{Budget, Exhausted};

    #[derive(Clone, Copy)]
    pub enum PlanNode {
        /// Halves an even value once.
        Halve,
        /// Subtracts one from an odd value above one once.
        Decrement,
        /// Components `components[start..start + count]`, in order.
        Sequence(usize, usize),
        /// The first of `components[start..start + count]` that fires.
        FirstOf(usize, usize),
        /// Node `.0` applied at most `.1` times.
        Repeat(usize, u32),
    }

    pub struct FlatPlan {
        pub nodes: Vec<PlanNode>,
        pub components: Vec<usize>,
    }

    #[derive(Clone, Copy)]
    pub enum PlanStatus {
        NoMatch,
        Applied,
        NormalForm,
        StepCap,
    }

    pub struct Firing {
        pub rule: u32,
        pub before: u64,
        pub after: u64,
    }

    pub struct Rewritten {
        pub value: u64,
        pub status: PlanStatus,
    }

    /// A node being interpreted: the components entered or the applications
    /// made so far, and the status so far.
    #[derive(Clone, Copy)]
    pub struct PlanFrame {
        pub node: usize,
        pub step: u32,
        pub status: PlanStatus,
    }

    fn fired(status: PlanStatus) -> bool {
        match status {
            PlanStatus::NoMatch => false,
            PlanStatus::Applied | PlanStatus::NormalForm | PlanStatus::StepCap => true,
        }
    }

    /// The status of a sequence after a component reported `next`.
    fn combine(so_far: PlanStatus, next: PlanStatus) -> PlanStatus {
        match so_far {
            PlanStatus::StepCap => PlanStatus::StepCap,
            _ => match next {
                PlanStatus::NoMatch => so_far,
                _ => next,
            },
        }
    }

    fn halve(value: u64, trace: &mut Vec<Firing>) -> Rewritten {
        if value > 0 && value % 2 != 1 {
            trace.push(Firing {
                rule: 0,
                before: value,
                after: value / 2,
            });
            return Rewritten {
                value: value / 2,
                status: PlanStatus::Applied,
            };
        }
        Rewritten {
            value,
            status: PlanStatus::NoMatch,
        }
    }

    fn decrement(value: u64, trace: &mut Vec<Firing>) -> Rewritten {
        if value % 2 == 1 && value > 1 {
            trace.push(Firing {
                rule: 1,
                before: value,
                after: value - 1,
            });
            return Rewritten {
                value: value - 1,
                status: PlanStatus::Applied,
            };
        }
        Rewritten {
            value,
            status: PlanStatus::NoMatch,
        }
    }

    fn put_frame(frames: &mut Vec<PlanFrame>, index: usize, frame: PlanFrame) {
        if index < frames.len() {
            frames[index] = frame;
        } else {
            frames.push(frame);
        }
    }

    fn enter(node: usize) -> PlanFrame {
        PlanFrame {
            node,
            step: 0,
            status: PlanStatus::NoMatch,
        }
    }

    /// Runs `plan` from node 0 on `value`; on failure no trace is returned and
    /// the input is unchanged.
    pub fn run(
        plan: &FlatPlan,
        value: u64,
        budget: &mut Budget,
    ) -> Result<(Rewritten, Vec<Firing>), Exhausted> {
        let mut trace = Vec::new();
        let mut frames = Vec::new();
        frames.push(enter(0));
        let mut depth = 1;
        let mut current = value;
        // The status of the frame that finished last, and whether the frame
        // below it has yet to receive it.
        let mut last = PlanStatus::NoMatch;
        let mut returning = false;
        while depth > 0 {
            budget.take(1)?;
            let top = depth - 1;
            let frame = frames[top];
            match plan.nodes[frame.node] {
                PlanNode::Halve => {
                    let result = halve(current, &mut trace);
                    current = result.value;
                    last = result.status;
                    returning = true;
                    depth -= 1;
                }
                PlanNode::Decrement => {
                    let result = decrement(current, &mut trace);
                    current = result.value;
                    last = result.status;
                    returning = true;
                    depth -= 1;
                }
                PlanNode::Sequence(start, count) => {
                    let status = if returning {
                        combine(frame.status, last)
                    } else {
                        frame.status
                    };
                    returning = false;
                    let index = frame.step as usize;
                    if index < count {
                        frames[top] = PlanFrame {
                            node: frame.node,
                            step: frame.step + 1,
                            status,
                        };
                        put_frame(&mut frames, depth, enter(plan.components[start + index]));
                        depth += 1;
                    } else {
                        last = status;
                        returning = true;
                        depth -= 1;
                    }
                }
                PlanNode::FirstOf(start, count) => {
                    let index = frame.step as usize;
                    if returning && fired(last) {
                        depth -= 1;
                    } else if index < count {
                        returning = false;
                        frames[top] = PlanFrame {
                            node: frame.node,
                            step: frame.step + 1,
                            status: frame.status,
                        };
                        put_frame(&mut frames, depth, enter(plan.components[start + index]));
                        depth += 1;
                    } else {
                        last = PlanStatus::NoMatch;
                        returning = true;
                        depth -= 1;
                    }
                }
                PlanNode::Repeat(inner, maximum) => {
                    let any = fired(frame.status);
                    if returning && !fired(last) {
                        last = if any {
                            PlanStatus::NormalForm
                        } else {
                            PlanStatus::NoMatch
                        };
                        depth -= 1;
                    } else {
                        let status = if returning {
                            PlanStatus::Applied
                        } else {
                            frame.status
                        };
                        returning = false;
                        if frame.step < maximum {
                            frames[top] = PlanFrame {
                                node: frame.node,
                                step: frame.step + 1,
                                status,
                            };
                            put_frame(&mut frames, depth, enter(inner));
                            depth += 1;
                        } else {
                            last = if fired(status) {
                                PlanStatus::StepCap
                            } else {
                                PlanStatus::NoMatch
                            };
                            returning = true;
                            depth -= 1;
                        }
                    }
                }
            }
        }
        Ok((
            Rewritten {
                value: current,
                status: last,
            },
            trace,
        ))
    }
}

/// The strategies of `strategy_data` as a recursive enumeration with boxed
/// and vector children, interpreted by a function recursive on the strategy
/// that walks the components of a sequence or an alternative, and repeats a
/// bounded repetition, by helpers recursive on an index or a count instead of
/// loops.
pub mod strategy_recursive {
    use crate::budget::{Budget, Exhausted};

    pub enum RecPlan {
        /// Halves an even value once.
        Halve,
        /// Subtracts one from an odd value above one once.
        Decrement,
        Sequence(Vec<RecPlan>),
        FirstOf(Vec<RecPlan>),
        Repeat(Box<RecPlan>, u32),
    }

    #[derive(Clone, Copy)]
    pub enum RecStatus {
        NoMatch,
        Applied,
        NormalForm,
        StepCap,
    }

    pub struct RecFiring {
        pub rule: u32,
        pub before: u64,
        pub after: u64,
    }

    pub struct RecRewritten {
        pub value: u64,
        pub status: RecStatus,
    }

    fn fired(status: RecStatus) -> bool {
        match status {
            RecStatus::NoMatch => false,
            RecStatus::Applied | RecStatus::NormalForm | RecStatus::StepCap => true,
        }
    }

    /// The status of a sequence after a component reported `next`.
    fn combine(so_far: RecStatus, next: RecStatus) -> RecStatus {
        match so_far {
            RecStatus::StepCap => RecStatus::StepCap,
            _ => match next {
                RecStatus::NoMatch => so_far,
                _ => next,
            },
        }
    }

    fn halve(value: u64, trace: &mut Vec<RecFiring>) -> RecRewritten {
        if value > 0 && value % 2 != 1 {
            trace.push(RecFiring {
                rule: 0,
                before: value,
                after: value / 2,
            });
            return RecRewritten {
                value: value / 2,
                status: RecStatus::Applied,
            };
        }
        RecRewritten {
            value,
            status: RecStatus::NoMatch,
        }
    }

    fn decrement(value: u64, trace: &mut Vec<RecFiring>) -> RecRewritten {
        if value % 2 == 1 && value > 1 {
            trace.push(RecFiring {
                rule: 1,
                before: value,
                after: value - 1,
            });
            return RecRewritten {
                value: value - 1,
                status: RecStatus::Applied,
            };
        }
        RecRewritten {
            value,
            status: RecStatus::NoMatch,
        }
    }

    pub fn apply(
        plan: &RecPlan,
        value: u64,
        trace: &mut Vec<RecFiring>,
        budget: &mut Budget,
    ) -> Result<RecRewritten, Exhausted> {
        budget.take(1)?;
        match plan {
            RecPlan::Halve => Ok(halve(value, trace)),
            RecPlan::Decrement => Ok(decrement(value, trace)),
            RecPlan::Sequence(plans) => {
                sequence(plans, 0, value, RecStatus::NoMatch, trace, budget)
            }
            RecPlan::FirstOf(plans) => first_of(plans, 0, value, trace, budget),
            RecPlan::Repeat(inner, maximum) => repeat(inner, *maximum, value, false, trace, budget),
        }
    }

    fn sequence(
        plans: &[RecPlan],
        index: usize,
        value: u64,
        status: RecStatus,
        trace: &mut Vec<RecFiring>,
        budget: &mut Budget,
    ) -> Result<RecRewritten, Exhausted> {
        if index >= plans.len() {
            return Ok(RecRewritten { value, status });
        }
        let result = apply(&plans[index], value, trace, budget)?;
        let status = combine(status, result.status);
        sequence(plans, index + 1, result.value, status, trace, budget)
    }

    fn first_of(
        plans: &[RecPlan],
        index: usize,
        value: u64,
        trace: &mut Vec<RecFiring>,
        budget: &mut Budget,
    ) -> Result<RecRewritten, Exhausted> {
        if index >= plans.len() {
            return Ok(RecRewritten {
                value,
                status: RecStatus::NoMatch,
            });
        }
        let result = apply(&plans[index], value, trace, budget)?;
        if fired(result.status) {
            return Ok(result);
        }
        first_of(plans, index + 1, value, trace, budget)
    }

    /// Applies `inner` at most `left` more times, recursive on `left`; `any`
    /// records whether an earlier application fired.
    fn repeat(
        inner: &RecPlan,
        left: u32,
        value: u64,
        any: bool,
        trace: &mut Vec<RecFiring>,
        budget: &mut Budget,
    ) -> Result<RecRewritten, Exhausted> {
        if left == 0 {
            let status = if any {
                RecStatus::StepCap
            } else {
                RecStatus::NoMatch
            };
            return Ok(RecRewritten { value, status });
        }
        let result = apply(inner, value, trace, budget)?;
        if !fired(result.status) {
            let status = if any {
                RecStatus::NormalForm
            } else {
                RecStatus::NoMatch
            };
            return Ok(RecRewritten { value, status });
        }
        repeat(inner, left - 1, result.value, true, trace, budget)
    }

    /// Runs `plan` on `value`; on failure no trace is returned and the input
    /// is unchanged.
    pub fn run(
        plan: &RecPlan,
        value: u64,
        budget: &mut Budget,
    ) -> Result<(RecRewritten, Vec<RecFiring>), Exhausted> {
        let mut trace = Vec::new();
        let result = apply(plan, value, &mut trace, budget)?;
        Ok((result, trace))
    }
}

/// The recursive interpreter of `strategy_recursive` with the components of a
/// sequence or an alternative, and the repetitions, walked by `while` loops in
/// helpers that call the interpreter, so that the recursion passes through the
/// loops.
pub mod strategy_loop {
    use crate::budget::{Budget, Exhausted};

    pub enum LoopPlan {
        /// Halves an even value once.
        Halve,
        /// Subtracts one from an odd value above one once.
        Decrement,
        Sequence(Vec<LoopPlan>),
        FirstOf(Vec<LoopPlan>),
        Repeat(Box<LoopPlan>, u32),
    }

    #[derive(Clone, Copy)]
    pub enum LoopStatus {
        NoMatch,
        Applied,
        NormalForm,
        StepCap,
    }

    pub struct LoopFiring {
        pub rule: u32,
        pub before: u64,
        pub after: u64,
    }

    pub struct LoopRewritten {
        pub value: u64,
        pub status: LoopStatus,
    }

    fn fired(status: LoopStatus) -> bool {
        match status {
            LoopStatus::NoMatch => false,
            LoopStatus::Applied | LoopStatus::NormalForm | LoopStatus::StepCap => true,
        }
    }

    /// The status of a sequence after a component reported `next`.
    fn combine(so_far: LoopStatus, next: LoopStatus) -> LoopStatus {
        match so_far {
            LoopStatus::StepCap => LoopStatus::StepCap,
            _ => match next {
                LoopStatus::NoMatch => so_far,
                _ => next,
            },
        }
    }

    fn halve(value: u64, trace: &mut Vec<LoopFiring>) -> LoopRewritten {
        if value > 0 && value % 2 != 1 {
            trace.push(LoopFiring {
                rule: 0,
                before: value,
                after: value / 2,
            });
            return LoopRewritten {
                value: value / 2,
                status: LoopStatus::Applied,
            };
        }
        LoopRewritten {
            value,
            status: LoopStatus::NoMatch,
        }
    }

    fn decrement(value: u64, trace: &mut Vec<LoopFiring>) -> LoopRewritten {
        if value % 2 == 1 && value > 1 {
            trace.push(LoopFiring {
                rule: 1,
                before: value,
                after: value - 1,
            });
            return LoopRewritten {
                value: value - 1,
                status: LoopStatus::Applied,
            };
        }
        LoopRewritten {
            value,
            status: LoopStatus::NoMatch,
        }
    }

    pub fn apply(
        plan: &LoopPlan,
        value: u64,
        trace: &mut Vec<LoopFiring>,
        budget: &mut Budget,
    ) -> Result<LoopRewritten, Exhausted> {
        budget.take(1)?;
        match plan {
            LoopPlan::Halve => Ok(halve(value, trace)),
            LoopPlan::Decrement => Ok(decrement(value, trace)),
            LoopPlan::Sequence(plans) => sequence(plans, value, trace, budget),
            LoopPlan::FirstOf(plans) => first_of(plans, value, trace, budget),
            LoopPlan::Repeat(inner, maximum) => repeat(inner, *maximum, value, trace, budget),
        }
    }

    fn sequence(
        plans: &[LoopPlan],
        value: u64,
        trace: &mut Vec<LoopFiring>,
        budget: &mut Budget,
    ) -> Result<LoopRewritten, Exhausted> {
        let mut current = value;
        let mut status = LoopStatus::NoMatch;
        let mut index = 0;
        while index < plans.len() {
            let result = apply(&plans[index], current, trace, budget)?;
            current = result.value;
            status = combine(status, result.status);
            index += 1;
        }
        Ok(LoopRewritten {
            value: current,
            status,
        })
    }

    fn first_of(
        plans: &[LoopPlan],
        value: u64,
        trace: &mut Vec<LoopFiring>,
        budget: &mut Budget,
    ) -> Result<LoopRewritten, Exhausted> {
        let mut index = 0;
        while index < plans.len() {
            let result = apply(&plans[index], value, trace, budget)?;
            if fired(result.status) {
                return Ok(result);
            }
            index += 1;
        }
        Ok(LoopRewritten {
            value,
            status: LoopStatus::NoMatch,
        })
    }

    fn repeat(
        inner: &LoopPlan,
        maximum: u32,
        value: u64,
        trace: &mut Vec<LoopFiring>,
        budget: &mut Budget,
    ) -> Result<LoopRewritten, Exhausted> {
        let mut current = value;
        let mut any = false;
        let mut count = 0;
        while count < maximum {
            let result = apply(inner, current, trace, budget)?;
            if !fired(result.status) {
                let status = if any {
                    LoopStatus::NormalForm
                } else {
                    LoopStatus::NoMatch
                };
                return Ok(LoopRewritten {
                    value: current,
                    status,
                });
            }
            current = result.value;
            any = true;
            count += 1;
        }
        let status = if any {
            LoopStatus::StepCap
        } else {
            LoopStatus::NoMatch
        };
        Ok(LoopRewritten {
            value: current,
            status,
        })
    }

    /// Runs `plan` on `value`; on failure no trace is returned and the input
    /// is unchanged.
    pub fn run(
        plan: &LoopPlan,
        value: u64,
        budget: &mut Budget,
    ) -> Result<(LoopRewritten, Vec<LoopFiring>), Exhausted> {
        let mut trace = Vec::new();
        let result = apply(plan, value, &mut trace, budget)?;
        Ok((result, trace))
    }
}

/// A sum assigned directly to a field of an element of a vector that a
/// structure holds, `self.slots[top].next = index + 1`, as the backtracking of
/// a matcher advances its choice point. Aeneas rejects the method; the same
/// assignment through a slice parameter, the compound assignment `+= 1` and
/// the assignment of a local holding the sum translate.
pub mod indexed_field_sum {
    pub struct ChoiceSlot {
        pub next: usize,
    }

    pub struct ChoiceStack {
        pub slots: Vec<ChoiceSlot>,
    }

    impl ChoiceStack {
        pub fn advance(&mut self, top: usize, index: usize) {
            self.slots[top].next = index + 1;
        }
    }

    pub fn advance_slice(slots: &mut [ChoiceSlot], top: usize, index: usize) {
        slots[top].next = index + 1;
    }
}

/// A collection value as a nested enumeration, generic over a trait of its
/// atoms: copying and three-valued equality without recursion, next to a
/// `Drop` implementation that releases through an owned stack. A record keeps
/// its keys and its values in two vectors, so the children of every container
/// form one slice of items, and each traversal is one loop over one stack of
/// tuples that hold a borrowed child slice, a position and owned data, each
/// tuple handled completely in the arm that pops it.
pub mod collection_tree_copy {
    use crate::budget::{Budget, Exhausted};

    pub enum Item<A> {
        Atom(A),
        List(Vec<Item<A>>),
        Record(Vec<String>, Vec<Item<A>>),
    }

    #[derive(Clone, Copy)]
    pub enum Answer {
        Yes,
        No,
        Unknown,
    }

    pub trait Atom: Clone {
        fn same(&self, other: &Self, budget: &mut Budget) -> Result<Answer, Exhausted>;
    }

    impl<A> Drop for Item<A> {
        fn drop(&mut self) {
            let mut stack = take_children(self);
            while let Some(mut item) = stack.pop() {
                let mut children = take_children(&mut item);
                stack.append(&mut children);
            }
        }
    }

    /// Moves the children of a container out, leaving it empty.
    fn take_children<A>(item: &mut Item<A>) -> Vec<Item<A>> {
        match item {
            Item::Atom(_) => Vec::new(),
            Item::List(items) | Item::Record(_, items) => std::mem::take(items),
        }
    }

    /// Type aliases only name the tuples; the tools see the tuples. A
    /// container being copied holds the copies of its keys if it is a
    /// record, its source elements, the next one to copy and the copies made.
    type Copying<'a, A> = (Option<Vec<String>>, &'a [Item<A>], usize, Vec<Item<A>>);
    type Pair<'a, A> = (&'a [Item<A>], &'a [Item<A>], usize);

    /// A copy of the elements `items`, charging one unit per step.
    pub fn copy_items<A: Atom>(
        items: &[Item<A>],
        budget: &mut Budget,
    ) -> Result<Vec<Item<A>>, Exhausted> {
        let mut result = Vec::new();
        let mut frames: Vec<Copying<'_, A>> = Vec::new();
        frames.push((None, items, 0, Vec::new()));
        while let Some((keys, items, next, mut built)) = frames.pop() {
            budget.take(1)?;
            if next < items.len() {
                match &items[next] {
                    Item::Atom(atom) => {
                        built.push(Item::Atom(atom.clone()));
                        frames.push((keys, items, next + 1, built));
                    }
                    Item::List(children) => {
                        frames.push((keys, items, next + 1, built));
                        frames.push((None, children, 0, Vec::new()));
                    }
                    Item::Record(names, children) => {
                        let copies = copy_keys(names, budget)?;
                        frames.push((keys, items, next + 1, built));
                        frames.push((Some(copies), children, 0, Vec::new()));
                    }
                }
            } else {
                let done = match keys {
                    Some(keys) => Item::Record(keys, built),
                    None => Item::List(built),
                };
                match frames.pop() {
                    Some((up_keys, up_items, up_next, mut siblings)) => {
                        siblings.push(done);
                        frames.push((up_keys, up_items, up_next, siblings));
                    }
                    None => result = take_children_of(done),
                }
            }
        }
        Ok(result)
    }

    fn take_children_of<A>(mut item: Item<A>) -> Vec<Item<A>> {
        take_children(&mut item)
    }

    fn copy_keys(keys: &[String], budget: &mut Budget) -> Result<Vec<String>, Exhausted> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < keys.len() {
            budget.take(1)?;
            copies.push(keys[index].clone());
            index += 1;
        }
        Ok(copies)
    }

    /// Three-valued structural equality: any difference outside the atoms
    /// answers no, and an unknown atom answer makes the result unknown.
    pub fn equal<A: Atom>(
        a: &Item<A>,
        b: &Item<A>,
        budget: &mut Budget,
    ) -> Result<Answer, Exhausted> {
        let mut answer = Answer::Yes;
        let mut pairs: Vec<Pair<'_, A>> = Vec::new();
        pairs.push((std::slice::from_ref(a), std::slice::from_ref(b), 0));
        while let Some((xs, ys, next)) = pairs.pop() {
            budget.take(1)?;
            if next < xs.len() {
                pairs.push((xs, ys, next + 1));
                match &xs[next] {
                    Item::Atom(p) => match &ys[next] {
                        Item::Atom(q) => match p.same(q, budget)? {
                            Answer::No => return Ok(Answer::No),
                            Answer::Unknown => answer = Answer::Unknown,
                            Answer::Yes => {}
                        },
                        _ => return Ok(Answer::No),
                    },
                    Item::List(cs) => match &ys[next] {
                        Item::List(ds) if cs.len() == ds.len() => pairs.push((cs, ds, 0)),
                        _ => return Ok(Answer::No),
                    },
                    Item::Record(ks, cs) => match &ys[next] {
                        Item::Record(ls, ds) if cs.len() == ds.len() => {
                            if !same_keys(ks, ls, budget)? {
                                return Ok(Answer::No);
                            }
                            pairs.push((cs, ds, 0));
                        }
                        _ => return Ok(Answer::No),
                    },
                }
            }
        }
        Ok(answer)
    }

    fn same_keys(a: &[String], b: &[String], budget: &mut Budget) -> Result<bool, Exhausted> {
        if a.len() != b.len() {
            return Ok(false);
        }
        let mut index = 0;
        while index < a.len() {
            budget.take(1)?;
            if a[index] != b[index] {
                return Ok(false);
            }
            index += 1;
        }
        Ok(true)
    }
}

/// The nested enumeration with records held in an ordered map: the nested
/// occurrence passes through a type that the tools leave external.
pub mod collection_tree_map {
    use std::collections::BTreeMap;

    pub enum Item<A> {
        Atom(A),
        List(Vec<Item<A>>),
        Record(BTreeMap<String, Item<A>>),
    }

    pub fn length<A>(item: &Item<A>) -> Option<usize> {
        match item {
            Item::Atom(_) => None,
            Item::List(items) => Some(items.len()),
            Item::Record(fields) => Some(fields.len()),
        }
    }
}

/// A traversal of the nested enumeration with an explicit stack of borrowed
/// items instead of recursion, charging one unit per item; a helper with a
/// loop pushes the children through a `&mut` reference to the stack.
pub mod collection_tree_walk {
    use crate::budget::{Budget, Exhausted};

    pub enum Item<A> {
        Atom(A),
        List(Vec<Item<A>>),
    }

    pub trait Atom {
        fn nodes(&self) -> u64;
    }

    pub fn nodes<A: Atom>(root: &Item<A>, budget: &mut Budget) -> Result<u64, Exhausted> {
        let mut stack: Vec<&Item<A>> = Vec::new();
        stack.push(root);
        let mut total = 0u64;
        while let Some(item) = stack.pop() {
            budget.take(1)?;
            match item {
                Item::Atom(atom) => total = total.saturating_add(atom.nodes()),
                Item::List(items) => {
                    total = total.saturating_add(1);
                    push_children(&mut stack, items);
                }
            }
        }
        Ok(total)
    }

    fn push_children<'a, A>(stack: &mut Vec<&'a Item<A>>, items: &'a [Item<A>]) {
        let mut index = 0;
        while index < items.len() {
            stack.push(&items[index]);
            index += 1;
        }
    }
}

/// Copying and three-valued equality of the nested enumeration over stacks of
/// frames that are enumerations with a lifetime parameter, which helpers take
/// and return.
pub mod collection_tree_frame_enum {
    use crate::budget::{Budget, Exhausted};

    pub enum Item<A> {
        Atom(A),
        List(Vec<Item<A>>),
        Record(Vec<(String, Item<A>)>),
    }

    #[derive(Clone, Copy)]
    pub enum Answer {
        Yes,
        No,
        Unknown,
    }

    pub trait Atom: Clone {
        fn same(&self, other: &Self, budget: &mut Budget) -> Result<Answer, Exhausted>;
    }

    /// A container being copied: its source entries, the next entry to copy
    /// and the copies made so far.
    enum Frame<'a, A> {
        List(&'a [Item<A>], usize, Vec<Item<A>>),
        Record(&'a [(String, Item<A>)], usize, Vec<(String, Item<A>)>),
    }

    pub fn copy<A: Atom>(root: &Item<A>, budget: &mut Budget) -> Result<Item<A>, Exhausted> {
        match root {
            Item::Atom(atom) => Ok(Item::Atom(atom.clone())),
            Item::List(items) => copy_frames(Frame::List(items, 0, Vec::new()), budget),
            Item::Record(fields) => copy_frames(Frame::Record(fields, 0, Vec::new()), budget),
        }
    }

    fn copy_frames<A: Atom>(
        first: Frame<'_, A>,
        budget: &mut Budget,
    ) -> Result<Item<A>, Exhausted> {
        let mut frames = Vec::new();
        frames.push(first);
        while let Some(frame) = frames.pop() {
            budget.take(1)?;
            let (source, frame) = next_source(frame);
            match source {
                Some(item) => match item {
                    Item::Atom(atom) => frames.push(attach(frame, Item::Atom(atom.clone()))),
                    Item::List(items) => {
                        frames.push(frame);
                        frames.push(Frame::List(items, 0, Vec::new()));
                    }
                    Item::Record(fields) => {
                        frames.push(frame);
                        frames.push(Frame::Record(fields, 0, Vec::new()));
                    }
                },
                None => {
                    let done = finish(frame);
                    match frames.pop() {
                        Some(parent) => frames.push(attach(parent, done)),
                        None => return Ok(done),
                    }
                }
            }
        }
        Ok(Item::List(Vec::new()))
    }

    /// The next source entry of a frame, if any.
    fn next_source<'a, A>(frame: Frame<'a, A>) -> (Option<&'a Item<A>>, Frame<'a, A>) {
        match frame {
            Frame::List(items, next, built) => {
                let source = if next < items.len() {
                    Some(&items[next])
                } else {
                    None
                };
                (source, Frame::List(items, next, built))
            }
            Frame::Record(fields, next, built) => {
                let source = if next < fields.len() {
                    Some(&fields[next].1)
                } else {
                    None
                };
                (source, Frame::Record(fields, next, built))
            }
        }
    }

    /// Stores the copy of the next entry and advances.
    fn attach<'a, A>(frame: Frame<'a, A>, copy: Item<A>) -> Frame<'a, A> {
        match frame {
            Frame::List(items, next, mut built) => {
                built.push(copy);
                Frame::List(items, next + 1, built)
            }
            Frame::Record(fields, next, mut built) => {
                built.push((fields[next].0.clone(), copy));
                Frame::Record(fields, next + 1, built)
            }
        }
    }

    fn finish<A>(frame: Frame<'_, A>) -> Item<A> {
        match frame {
            Frame::List(_, _, built) => Item::List(built),
            Frame::Record(_, _, built) => Item::Record(built),
        }
    }

    /// Two containers being compared, entry by entry.
    enum Pair<'a, A> {
        Lists(&'a [Item<A>], &'a [Item<A>], usize),
        Records(&'a [(String, Item<A>)], &'a [(String, Item<A>)], usize),
    }

    /// What comparing two entries yields: an answer, or a pair of containers
    /// of the same kind and length to compare next.
    enum Compared<'a, A> {
        Answer(Answer),
        Descend(Pair<'a, A>),
    }

    pub fn equal<A: Atom>(
        a: &Item<A>,
        b: &Item<A>,
        budget: &mut Budget,
    ) -> Result<Answer, Exhausted> {
        match compare(a, b, budget)? {
            Compared::Answer(answer) => Ok(answer),
            Compared::Descend(pair) => equal_pairs(pair, budget),
        }
    }

    fn equal_pairs<A: Atom>(first: Pair<'_, A>, budget: &mut Budget) -> Result<Answer, Exhausted> {
        let mut answer = Answer::Yes;
        let mut pairs = Vec::new();
        pairs.push(first);
        while let Some(pair) = pairs.pop() {
            budget.take(1)?;
            match pair {
                Pair::Lists(xs, ys, next) => {
                    if next < xs.len() {
                        pairs.push(Pair::Lists(xs, ys, next + 1));
                        match compare(&xs[next], &ys[next], budget)? {
                            Compared::Answer(Answer::No) => return Ok(Answer::No),
                            Compared::Answer(Answer::Unknown) => answer = Answer::Unknown,
                            Compared::Answer(Answer::Yes) => {}
                            Compared::Descend(inner) => pairs.push(inner),
                        }
                    }
                }
                Pair::Records(xs, ys, next) => {
                    if next < xs.len() {
                        if xs[next].0 != ys[next].0 {
                            return Ok(Answer::No);
                        }
                        pairs.push(Pair::Records(xs, ys, next + 1));
                        match compare(&xs[next].1, &ys[next].1, budget)? {
                            Compared::Answer(Answer::No) => return Ok(Answer::No),
                            Compared::Answer(Answer::Unknown) => answer = Answer::Unknown,
                            Compared::Answer(Answer::Yes) => {}
                            Compared::Descend(inner) => pairs.push(inner),
                        }
                    }
                }
            }
        }
        Ok(answer)
    }

    /// Compares two entries without descending: atoms by their test, other
    /// kinds by constructor and length.
    fn compare<'a, A: Atom>(
        x: &'a Item<A>,
        y: &'a Item<A>,
        budget: &mut Budget,
    ) -> Result<Compared<'a, A>, Exhausted> {
        match x {
            Item::Atom(p) => match y {
                Item::Atom(q) => Ok(Compared::Answer(p.same(q, budget)?)),
                _ => Ok(Compared::Answer(Answer::No)),
            },
            Item::List(xs) => match y {
                Item::List(ys) if xs.len() == ys.len() => {
                    Ok(Compared::Descend(Pair::Lists(xs, ys, 0)))
                }
                _ => Ok(Compared::Answer(Answer::No)),
            },
            Item::Record(xs) => match y {
                Item::Record(ys) if xs.len() == ys.len() => {
                    Ok(Compared::Descend(Pair::Records(xs, ys, 0)))
                }
                _ => Ok(Compared::Answer(Answer::No)),
            },
        }
    }
}

/// Strings as Unicode scalar values over their UTF-8 bytes: an index loop
/// that counts the bytes that start a character, and a slice taken by byte
/// offsets found the same way.
pub mod string_bytes {
    use crate::budget::{Budget, Exhausted};

    fn starts_character(byte: u8) -> bool {
        byte & 0xC0 != 0x80
    }

    pub fn count(text: &str, budget: &mut Budget) -> Result<usize, Exhausted> {
        let bytes = text.as_bytes();
        let mut count = 0;
        let mut index = 0;
        while index < bytes.len() {
            budget.take(1)?;
            if starts_character(bytes[index]) {
                count += 1;
            }
            index += 1;
        }
        Ok(count)
    }

    /// The byte offset of character `position`, or the length.
    pub fn offset(text: &str, position: usize, budget: &mut Budget) -> Result<usize, Exhausted> {
        let bytes = text.as_bytes();
        let mut seen = 0;
        let mut index = 0;
        while index < bytes.len() {
            budget.take(1)?;
            if starts_character(bytes[index]) {
                if seen == position {
                    return Ok(index);
                }
                seen += 1;
            }
            index += 1;
        }
        Ok(bytes.len())
    }

    pub fn slice(
        text: &str,
        lo: usize,
        hi: usize,
        budget: &mut Budget,
    ) -> Result<String, Exhausted> {
        let start = offset(text, lo, budget)?;
        let end = offset(text, hi, budget)?;
        Ok(text[start..end].to_owned())
    }
}

/// Strings as Unicode scalar values: counting and slicing by character
/// position over the `chars` iterator, one unit per character.
pub mod string_chars {
    use crate::budget::{Budget, Exhausted};

    pub fn count(text: &str, budget: &mut Budget) -> Result<usize, Exhausted> {
        let mut count = 0;
        for _ in text.chars() {
            budget.take(1)?;
            count += 1;
        }
        Ok(count)
    }

    /// The `count` characters from position `lo`, as a new string.
    pub fn slice(
        text: &str,
        lo: usize,
        count: usize,
        budget: &mut Budget,
    ) -> Result<String, Exhausted> {
        let mut out = String::new();
        let mut skip = lo;
        let mut take = count;
        for ch in text.chars() {
            budget.take(1)?;
            if take == 0 {
                break;
            }
            if skip > 0 {
                skip -= 1;
            } else {
                out.push(ch);
                take -= 1;
            }
        }
        Ok(out)
    }
}

/// The stored form of collection values with all its kinds, generic over a
/// trait of its atoms: strings, lists, tuples, records and maps that keep
/// their keys and their values in two vectors, and arrays that hold their
/// extents and a vector of atoms. Copying, three-valued equality, costs and
/// revalidation are free functions, each one loop over one stack of tuples
/// that hold a borrowed child slice, a position and owned partial results;
/// the copy frame also holds the kind of the container and the copied keys.
/// Range copies and costs call the whole-slice functions on one element at a
/// time instead of indexing a range of the slice. The check of a cost against
/// the value budget answers with a fieldless enumeration, so no string
/// literal is involved, and the costs of records, maps and arrays only stand
/// in for theirs.
pub mod collection_tree_kinds {
    pub enum KindsTree<A> {
        Atom(A),
        Text(String),
        List(Vec<KindsTree<A>>),
        Tuple(Vec<KindsTree<A>>),
        Record(Vec<String>, Vec<KindsTree<A>>),
        Map(Vec<String>, Vec<KindsTree<A>>),
        Array(Vec<usize>, Vec<A>),
    }

    /// The kind of a container whose children nest.
    #[derive(Clone, Copy)]
    pub enum KindsShape {
        List,
        Tuple,
        Record,
        Map,
    }

    #[derive(Clone, Copy)]
    pub enum KindsTruth {
        True,
        False,
        Unknown,
    }

    #[derive(Clone, Copy)]
    pub enum SliceBounds {
        Within,
        EndBeyond,
        StartAfterEnd,
    }

    #[derive(Clone, Copy)]
    pub enum Admission {
        Admitted,
        ValueNodes,
        ValueBytes,
    }

    #[derive(Clone, Copy)]
    pub enum KindsFault {
        Exhausted,
        Temporaries,
        Rejected,
    }

    #[derive(Clone, Copy)]
    pub struct KindsCost {
        pub nodes: usize,
        pub bytes: usize,
    }

    pub struct KindsLimits {
        pub max_nodes: usize,
        pub max_environment_nodes: usize,
        pub max_symbolic_bytes: usize,
        pub max_environment_bytes: usize,
    }

    /// A stand-in for the request context: the work left, the limits and the
    /// cost of the active frames.
    pub struct KindsContext {
        pub left: u64,
        pub limits: KindsLimits,
        pub frame_nodes: usize,
        pub frame_bytes: usize,
    }

    impl KindsContext {
        pub fn charge(&mut self, amount: u64) -> Result<(), KindsFault> {
            if amount > self.left {
                return Err(KindsFault::Exhausted);
            }
            self.left -= amount;
            Ok(())
        }

        pub fn limits(&self) -> &KindsLimits {
            &self.limits
        }

        /// Checks a temporary value together with the active frames.
        pub fn check_call_temporary(&self, nodes: usize, bytes: usize) -> Result<(), KindsFault> {
            let total_nodes = nodes.saturating_add(self.frame_nodes);
            let total_bytes = bytes.saturating_add(self.frame_bytes);
            if total_nodes > self.limits.max_environment_nodes
                || total_bytes > self.limits.max_environment_bytes
            {
                return Err(KindsFault::Temporaries);
            }
            Ok(())
        }
    }

    /// What collections need of atoms.
    pub trait Atom: Sized {
        /// Validates, charges and returns the cost, at least one node.
        fn cost(&self, context: &mut KindsContext) -> Result<KindsCost, KindsFault>;
        /// Revalidates under the receiving limits.
        fn check(&self, context: &mut KindsContext) -> Result<(), KindsFault>;
        fn same(&self, other: &Self, context: &mut KindsContext) -> Result<KindsTruth, KindsFault>;
        /// An uncharged copy; callers charge the cost first.
        fn duplicate(&self) -> Self;
    }

    impl<A> Drop for KindsTree<A> {
        fn drop(&mut self) {
            let mut stack = take_children(self);
            while let Some(mut item) = stack.pop() {
                let mut children = take_children(&mut item);
                stack.append(&mut children);
            }
        }
    }

    /// Moves the children of a container out, leaving it empty.
    fn take_children<A>(item: &mut KindsTree<A>) -> Vec<KindsTree<A>> {
        match item {
            KindsTree::List(items)
            | KindsTree::Tuple(items)
            | KindsTree::Record(_, items)
            | KindsTree::Map(_, items) => std::mem::take(items),
            KindsTree::Atom(_) | KindsTree::Text(_) | KindsTree::Array(_, _) => Vec::new(),
        }
    }

    fn take_children_of<A>(mut item: KindsTree<A>) -> Vec<KindsTree<A>> {
        take_children(&mut item)
    }

    fn smaller(a: usize, b: usize) -> usize {
        if a < b { a } else { b }
    }

    /// The sum of two costs, or `None` when it overflows.
    pub fn add_cost(a: KindsCost, b: KindsCost) -> Option<KindsCost> {
        match (a.nodes.checked_add(b.nodes), a.bytes.checked_add(b.bytes)) {
            (Some(nodes), Some(bytes)) => Some(KindsCost { nodes, bytes }),
            _ => None,
        }
    }

    /// The overhead of a container.
    fn container() -> KindsCost {
        KindsCost { nodes: 1, bytes: 8 }
    }

    /// Type aliases only name the tuples; the tools see the tuples. A
    /// container being copied holds its kind, the copies of its keys if it
    /// has keys, its source elements, the next one to copy and the copies
    /// made.
    type Copying<'a, A> = (
        KindsShape,
        Option<Vec<String>>,
        &'a [KindsTree<A>],
        usize,
        Vec<KindsTree<A>>,
    );
    type Pair<'a, A> = (&'a [KindsTree<A>], &'a [KindsTree<A>], usize);
    type Walk<'a, A> = (&'a [KindsTree<A>], usize);

    /// A copy of the elements `items`, charging one unit per step.
    pub fn copy_items<A: Atom>(
        items: &[KindsTree<A>],
        context: &mut KindsContext,
    ) -> Result<Vec<KindsTree<A>>, KindsFault> {
        let mut result = Vec::new();
        let mut frames: Vec<Copying<'_, A>> = Vec::new();
        frames.push((KindsShape::List, None, items, 0, Vec::new()));
        while let Some((shape, keys, items, next, mut built)) = frames.pop() {
            context.charge(1)?;
            if next < items.len() {
                match &items[next] {
                    KindsTree::Atom(atom) => {
                        built.push(KindsTree::Atom(atom.duplicate()));
                        frames.push((shape, keys, items, next + 1, built));
                    }
                    KindsTree::Text(text) => {
                        built.push(KindsTree::Text(text.clone()));
                        frames.push((shape, keys, items, next + 1, built));
                    }
                    KindsTree::List(children) => {
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::List, None, children, 0, Vec::new()));
                    }
                    KindsTree::Tuple(children) => {
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::Tuple, None, children, 0, Vec::new()));
                    }
                    KindsTree::Record(names, children) => {
                        let copies = copy_keys(names, context)?;
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::Record, Some(copies), children, 0, Vec::new()));
                    }
                    KindsTree::Map(names, children) => {
                        let copies = copy_keys(names, context)?;
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::Map, Some(copies), children, 0, Vec::new()));
                    }
                    KindsTree::Array(extents, atoms) => {
                        let copy = copy_array(extents, atoms, context)?;
                        built.push(copy);
                        frames.push((shape, keys, items, next + 1, built));
                    }
                }
            } else {
                let done = finish(shape, keys, built);
                match frames.pop() {
                    Some((up_shape, up_keys, up_items, up_next, mut siblings)) => {
                        siblings.push(done);
                        frames.push((up_shape, up_keys, up_items, up_next, siblings));
                    }
                    None => result = take_children_of(done),
                }
            }
        }
        Ok(result)
    }

    /// The container of kind `shape` with the copied keys and elements: a
    /// record or map has keys, a list or tuple has none.
    fn finish<A>(
        shape: KindsShape,
        keys: Option<Vec<String>>,
        built: Vec<KindsTree<A>>,
    ) -> KindsTree<A> {
        match keys {
            Some(keys) => match shape {
                KindsShape::Map => KindsTree::Map(keys, built),
                KindsShape::List | KindsShape::Tuple | KindsShape::Record => {
                    KindsTree::Record(keys, built)
                }
            },
            None => match shape {
                KindsShape::Tuple => KindsTree::Tuple(built),
                KindsShape::List | KindsShape::Record | KindsShape::Map => KindsTree::List(built),
            },
        }
    }

    fn copy_keys(keys: &[String], context: &mut KindsContext) -> Result<Vec<String>, KindsFault> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < keys.len() {
            context.charge(1)?;
            copies.push(keys[index].clone());
            index += 1;
        }
        Ok(copies)
    }

    fn copy_array<A: Atom>(
        extents: &[usize],
        atoms: &[A],
        context: &mut KindsContext,
    ) -> Result<KindsTree<A>, KindsFault> {
        let shape = copy_extents(extents);
        let copies = copy_atoms(atoms, context)?;
        Ok(KindsTree::Array(shape, copies))
    }

    fn copy_extents(extents: &[usize]) -> Vec<usize> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < extents.len() {
            copies.push(extents[index]);
            index += 1;
        }
        copies
    }

    fn copy_atoms<A: Atom>(atoms: &[A], context: &mut KindsContext) -> Result<Vec<A>, KindsFault> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < atoms.len() {
            context.charge(1)?;
            copies.push(atoms[index].duplicate());
            index += 1;
        }
        Ok(copies)
    }

    /// A copy of the elements from `lo` up to but excluding `hi`, one
    /// element at a time; the caller has checked the bounds.
    pub fn copy_range<A: Atom>(
        items: &[KindsTree<A>],
        lo: usize,
        hi: usize,
        context: &mut KindsContext,
    ) -> Result<Vec<KindsTree<A>>, KindsFault> {
        let mut result = Vec::new();
        let mut index = lo;
        while index < hi {
            let mut copies = copy_items(std::slice::from_ref(&items[index]), context)?;
            result.append(&mut copies);
            index += 1;
        }
        Ok(result)
    }

    /// Three-valued structural equality of two element slices: any
    /// difference outside the atoms answers false, and an unknown atom
    /// answer makes the result unknown.
    pub fn equal_items<A: Atom>(
        left: &[KindsTree<A>],
        right: &[KindsTree<A>],
        context: &mut KindsContext,
    ) -> Result<KindsTruth, KindsFault> {
        if left.len() != right.len() {
            return Ok(KindsTruth::False);
        }
        equal_walk(left, right, context)
    }

    fn equal_walk<A: Atom>(
        left: &[KindsTree<A>],
        right: &[KindsTree<A>],
        context: &mut KindsContext,
    ) -> Result<KindsTruth, KindsFault> {
        let mut answer = KindsTruth::True;
        let mut pairs: Vec<Pair<'_, A>> = Vec::new();
        pairs.push((left, right, 0));
        while let Some((xs, ys, next)) = pairs.pop() {
            context.charge(1)?;
            if next < xs.len() {
                pairs.push((xs, ys, next + 1));
                match &xs[next] {
                    KindsTree::Atom(p) => match &ys[next] {
                        KindsTree::Atom(q) => match p.same(q, context)? {
                            KindsTruth::False => return Ok(KindsTruth::False),
                            KindsTruth::Unknown => answer = KindsTruth::Unknown,
                            KindsTruth::True => {}
                        },
                        _ => return Ok(KindsTruth::False),
                    },
                    KindsTree::Text(a) => match &ys[next] {
                        KindsTree::Text(b) => {
                            let bytes = smaller(a.len(), b.len()) as u64;
                            context.charge(bytes.saturating_add(1))?;
                            if a != b {
                                return Ok(KindsTruth::False);
                            }
                        }
                        _ => return Ok(KindsTruth::False),
                    },
                    KindsTree::List(cs) => match &ys[next] {
                        KindsTree::List(ds) if cs.len() == ds.len() => pairs.push((cs, ds, 0)),
                        _ => return Ok(KindsTruth::False),
                    },
                    KindsTree::Tuple(cs) => match &ys[next] {
                        KindsTree::Tuple(ds) if cs.len() == ds.len() => pairs.push((cs, ds, 0)),
                        _ => return Ok(KindsTruth::False),
                    },
                    KindsTree::Record(ks, cs) => match &ys[next] {
                        KindsTree::Record(ls, ds) if cs.len() == ds.len() => {
                            if !same_keys(ks, ls, context)? {
                                return Ok(KindsTruth::False);
                            }
                            pairs.push((cs, ds, 0));
                        }
                        _ => return Ok(KindsTruth::False),
                    },
                    KindsTree::Map(ks, cs) => match &ys[next] {
                        KindsTree::Map(ls, ds) if cs.len() == ds.len() => {
                            if !same_keys(ks, ls, context)? {
                                return Ok(KindsTruth::False);
                            }
                            pairs.push((cs, ds, 0));
                        }
                        _ => return Ok(KindsTruth::False),
                    },
                    KindsTree::Array(es, xs_atoms) => match &ys[next] {
                        KindsTree::Array(fs, ys_atoms) => {
                            match equal_arrays(es, xs_atoms, fs, ys_atoms, context)? {
                                KindsTruth::False => return Ok(KindsTruth::False),
                                KindsTruth::Unknown => answer = KindsTruth::Unknown,
                                KindsTruth::True => {}
                            }
                        }
                        _ => return Ok(KindsTruth::False),
                    },
                }
            }
        }
        Ok(answer)
    }

    fn same_keys(
        a: &[String],
        b: &[String],
        context: &mut KindsContext,
    ) -> Result<bool, KindsFault> {
        if a.len() != b.len() {
            return Ok(false);
        }
        same_key_walk(a, b, context)
    }

    fn same_key_walk(
        a: &[String],
        b: &[String],
        context: &mut KindsContext,
    ) -> Result<bool, KindsFault> {
        let mut index = 0;
        while index < a.len() {
            context.charge(1)?;
            if a[index] != b[index] {
                return Ok(false);
            }
            index += 1;
        }
        Ok(true)
    }

    fn equal_arrays<A: Atom>(
        es: &[usize],
        xs: &[A],
        fs: &[usize],
        ys: &[A],
        context: &mut KindsContext,
    ) -> Result<KindsTruth, KindsFault> {
        if es.len() != fs.len() || xs.len() != ys.len() || !same_extents(es, fs) {
            return Ok(KindsTruth::False);
        }
        equal_atoms(xs, ys, context)
    }

    fn same_extents(es: &[usize], fs: &[usize]) -> bool {
        let mut index = 0;
        while index < es.len() {
            if es[index] != fs[index] {
                return false;
            }
            index += 1;
        }
        true
    }

    fn equal_atoms<A: Atom>(
        xs: &[A],
        ys: &[A],
        context: &mut KindsContext,
    ) -> Result<KindsTruth, KindsFault> {
        let mut answer = KindsTruth::True;
        let mut index = 0;
        while index < xs.len() {
            match xs[index].same(&ys[index], context)? {
                KindsTruth::False => return Ok(KindsTruth::False),
                KindsTruth::Unknown => answer = KindsTruth::Unknown,
                KindsTruth::True => {}
            }
            index += 1;
        }
        Ok(answer)
    }

    /// The cost of the elements `items`, or `None` when a sum overflows.
    pub fn cost_items<A: Atom>(
        items: &[KindsTree<A>],
        context: &mut KindsContext,
    ) -> Result<Option<KindsCost>, KindsFault> {
        let mut total = KindsCost { nodes: 0, bytes: 0 };
        let mut frames: Vec<Walk<'_, A>> = Vec::new();
        frames.push((items, 0));
        while let Some((items, next)) = frames.pop() {
            context.charge(1)?;
            if next < items.len() {
                frames.push((items, next + 1));
                let part = match &items[next] {
                    KindsTree::Atom(atom) => atom.cost(context)?,
                    KindsTree::Text(text) => match text.len().checked_add(8) {
                        Some(bytes) => KindsCost { nodes: 1, bytes },
                        None => return Ok(None),
                    },
                    KindsTree::List(children) | KindsTree::Tuple(children) => {
                        frames.push((children, 0));
                        container()
                    }
                    KindsTree::Record(keys, children) | KindsTree::Map(keys, children) => {
                        frames.push((children, 0));
                        match key_cost(keys, context)? {
                            Some(cost) => cost,
                            None => return Ok(None),
                        }
                    }
                    KindsTree::Array(_, atoms) => match atoms_cost(atoms, context)? {
                        Some(cost) => cost,
                        None => return Ok(None),
                    },
                };
                total = match add_cost(total, part) {
                    Some(sum) => sum,
                    None => return Ok(None),
                };
            }
        }
        Ok(Some(total))
    }

    /// The overhead of a record or map with the bytes of its keys.
    fn key_cost(
        keys: &[String],
        context: &mut KindsContext,
    ) -> Result<Option<KindsCost>, KindsFault> {
        let mut total = container();
        let mut index = 0;
        while index < keys.len() {
            context.charge(1)?;
            total = match total.bytes.checked_add(keys[index].len()) {
                Some(bytes) => KindsCost {
                    nodes: total.nodes,
                    bytes,
                },
                None => return Ok(None),
            };
            index += 1;
        }
        Ok(Some(total))
    }

    /// The overhead of an array with the costs of its atoms.
    fn atoms_cost<A: Atom>(
        atoms: &[A],
        context: &mut KindsContext,
    ) -> Result<Option<KindsCost>, KindsFault> {
        let mut total = container();
        let mut index = 0;
        while index < atoms.len() {
            let part = atoms[index].cost(context)?;
            total = match add_cost(total, part) {
                Some(sum) => sum,
                None => return Ok(None),
            };
            index += 1;
        }
        Ok(Some(total))
    }

    /// The cost of the elements from `lo` up to but excluding `hi`, one
    /// element at a time; the caller has checked the bounds.
    pub fn cost_range<A: Atom>(
        items: &[KindsTree<A>],
        lo: usize,
        hi: usize,
        context: &mut KindsContext,
    ) -> Result<Option<KindsCost>, KindsFault> {
        let mut total = KindsCost { nodes: 0, bytes: 0 };
        let mut index = lo;
        while index < hi {
            let part = match cost_items(std::slice::from_ref(&items[index]), context)? {
                Some(cost) => cost,
                None => return Ok(None),
            };
            total = match add_cost(total, part) {
                Some(sum) => sum,
                None => return Ok(None),
            };
            index += 1;
        }
        Ok(Some(total))
    }

    /// Revalidates every atom of the elements `items` under the limits of
    /// `context`.
    pub fn check_items<A: Atom>(
        items: &[KindsTree<A>],
        context: &mut KindsContext,
    ) -> Result<(), KindsFault> {
        let mut frames: Vec<Walk<'_, A>> = Vec::new();
        frames.push((items, 0));
        while let Some((items, next)) = frames.pop() {
            context.charge(1)?;
            if next < items.len() {
                frames.push((items, next + 1));
                match &items[next] {
                    KindsTree::Atom(atom) => atom.check(context)?,
                    KindsTree::Text(_) => {}
                    KindsTree::List(children)
                    | KindsTree::Tuple(children)
                    | KindsTree::Record(_, children)
                    | KindsTree::Map(_, children) => frames.push((children, 0)),
                    KindsTree::Array(_, atoms) => check_atoms(atoms, context)?,
                }
            }
        }
        Ok(())
    }

    fn check_atoms<A: Atom>(atoms: &[A], context: &mut KindsContext) -> Result<(), KindsFault> {
        let mut index = 0;
        while index < atoms.len() {
            atoms[index].check(context)?;
            index += 1;
        }
        Ok(())
    }

    /// Where the range from `lo` up to but excluding `hi` lies in a value
    /// of length `length`.
    pub fn slice_bounds(length: usize, lo: usize, hi: usize) -> SliceBounds {
        if hi > length {
            SliceBounds::EndBeyond
        } else if lo > hi {
            SliceBounds::StartAfterEnd
        } else {
            SliceBounds::Within
        }
    }

    /// The copies of `left` followed by the copies of `right`.
    pub fn concat_items<A: Atom>(
        left: &[KindsTree<A>],
        right: &[KindsTree<A>],
        context: &mut KindsContext,
    ) -> Result<Vec<KindsTree<A>>, KindsFault> {
        let mut result = copy_items(left, context)?;
        let mut tail = copy_items(right, context)?;
        result.append(&mut tail);
        Ok(result)
    }

    /// Checks a cost against the value budget, the smaller of the value and
    /// environment limits, and then together with the active frames.
    pub fn admit(cost: KindsCost, context: &mut KindsContext) -> Result<Admission, KindsFault> {
        let limits = context.limits();
        let nodes = smaller(limits.max_nodes, limits.max_environment_nodes);
        let bytes = smaller(limits.max_symbolic_bytes, limits.max_environment_bytes);
        if cost.nodes > nodes {
            return Ok(Admission::ValueNodes);
        }
        if cost.bytes > bytes {
            return Ok(Admission::ValueBytes);
        }
        context.check_call_temporary(cost.nodes, cost.bytes)?;
        Ok(Admission::Admitted)
    }

    /// The concatenation of two strings, charged by its length. The sum of
    /// two string lengths cannot overflow, since each is at most
    /// `isize::MAX`.
    pub fn concat_text(a: &str, b: &str, context: &mut KindsContext) -> Result<String, KindsFault> {
        let length = a.len() + b.len();
        context.charge(length as u64)?;
        let mut text = String::with_capacity(length);
        text.push_str(a);
        text.push_str(b);
        Ok(text)
    }
}

/// Hand-written `Clone`, `PartialEq`, `Eq` and `Debug` for the stored form of
/// `collection_tree_kinds`, since derived implementations recurse: each
/// delegates to an uncharged worklist of the same form as the charged
/// traversals, and `Debug` writes through the standard formatter, with frames
/// of a kind, a borrowed slice of elements and a position.
pub mod collection_hand_traits {
    use crate::collection_tree_kinds::{KindsShape, KindsTree};
    use std::fmt;

    impl<A: Clone> Clone for KindsTree<A> {
        fn clone(&self) -> Self {
            let mut copies = clone_items(std::slice::from_ref(self));
            match copies.pop() {
                Some(copy) => copy,
                None => KindsTree::List(Vec::new()),
            }
        }
    }

    impl<A: PartialEq> PartialEq for KindsTree<A> {
        fn eq(&self, other: &Self) -> bool {
            eq_items(std::slice::from_ref(self), std::slice::from_ref(other))
        }
    }

    impl<A: Eq> Eq for KindsTree<A> {}

    impl<A: fmt::Debug> fmt::Debug for KindsTree<A> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            debug_items(std::slice::from_ref(self), f)
        }
    }

    type Cloning<'a, A> = (
        KindsShape,
        Option<Vec<String>>,
        &'a [KindsTree<A>],
        usize,
        Vec<KindsTree<A>>,
    );
    type Comparing<'a, A> = (&'a [KindsTree<A>], &'a [KindsTree<A>], usize);
    type Writing<'a, A> = (KindsShape, &'a [KindsTree<A>], usize);

    fn take_children<A>(item: &mut KindsTree<A>) -> Vec<KindsTree<A>> {
        match item {
            KindsTree::List(items)
            | KindsTree::Tuple(items)
            | KindsTree::Record(_, items)
            | KindsTree::Map(_, items) => std::mem::take(items),
            KindsTree::Atom(_) | KindsTree::Text(_) | KindsTree::Array(_, _) => Vec::new(),
        }
    }

    fn take_children_of<A>(mut item: KindsTree<A>) -> Vec<KindsTree<A>> {
        take_children(&mut item)
    }

    fn finish<A>(
        shape: KindsShape,
        keys: Option<Vec<String>>,
        built: Vec<KindsTree<A>>,
    ) -> KindsTree<A> {
        match keys {
            Some(keys) => match shape {
                KindsShape::Map => KindsTree::Map(keys, built),
                KindsShape::List | KindsShape::Tuple | KindsShape::Record => {
                    KindsTree::Record(keys, built)
                }
            },
            None => match shape {
                KindsShape::Tuple => KindsTree::Tuple(built),
                KindsShape::List | KindsShape::Record | KindsShape::Map => KindsTree::List(built),
            },
        }
    }

    /// An uncharged copy of the elements `items`.
    pub fn clone_items<A: Clone>(items: &[KindsTree<A>]) -> Vec<KindsTree<A>> {
        let mut result = Vec::new();
        let mut frames: Vec<Cloning<'_, A>> = Vec::new();
        frames.push((KindsShape::List, None, items, 0, Vec::new()));
        while let Some((shape, keys, items, next, mut built)) = frames.pop() {
            if next < items.len() {
                match &items[next] {
                    KindsTree::Atom(atom) => {
                        built.push(KindsTree::Atom(atom.clone()));
                        frames.push((shape, keys, items, next + 1, built));
                    }
                    KindsTree::Text(text) => {
                        built.push(KindsTree::Text(text.clone()));
                        frames.push((shape, keys, items, next + 1, built));
                    }
                    KindsTree::List(children) => {
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::List, None, children, 0, Vec::new()));
                    }
                    KindsTree::Tuple(children) => {
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::Tuple, None, children, 0, Vec::new()));
                    }
                    KindsTree::Record(names, children) => {
                        let copies = clone_keys(names);
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::Record, Some(copies), children, 0, Vec::new()));
                    }
                    KindsTree::Map(names, children) => {
                        let copies = clone_keys(names);
                        frames.push((shape, keys, items, next + 1, built));
                        frames.push((KindsShape::Map, Some(copies), children, 0, Vec::new()));
                    }
                    KindsTree::Array(extents, atoms) => {
                        built.push(KindsTree::Array(clone_extents(extents), clone_atoms(atoms)));
                        frames.push((shape, keys, items, next + 1, built));
                    }
                }
            } else {
                let done = finish(shape, keys, built);
                match frames.pop() {
                    Some((up_shape, up_keys, up_items, up_next, mut siblings)) => {
                        siblings.push(done);
                        frames.push((up_shape, up_keys, up_items, up_next, siblings));
                    }
                    None => result = take_children_of(done),
                }
            }
        }
        result
    }

    fn clone_keys(keys: &[String]) -> Vec<String> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < keys.len() {
            copies.push(keys[index].clone());
            index += 1;
        }
        copies
    }

    fn clone_extents(extents: &[usize]) -> Vec<usize> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < extents.len() {
            copies.push(extents[index]);
            index += 1;
        }
        copies
    }

    fn clone_atoms<A: Clone>(atoms: &[A]) -> Vec<A> {
        let mut copies = Vec::new();
        let mut index = 0;
        while index < atoms.len() {
            copies.push(atoms[index].clone());
            index += 1;
        }
        copies
    }

    /// Uncharged equality of stored forms.
    pub fn eq_items<A: PartialEq>(left: &[KindsTree<A>], right: &[KindsTree<A>]) -> bool {
        if left.len() != right.len() {
            return false;
        }
        eq_walk(left, right)
    }

    fn eq_walk<A: PartialEq>(left: &[KindsTree<A>], right: &[KindsTree<A>]) -> bool {
        let mut pairs: Vec<Comparing<'_, A>> = Vec::new();
        pairs.push((left, right, 0));
        while let Some((xs, ys, next)) = pairs.pop() {
            if next < xs.len() {
                pairs.push((xs, ys, next + 1));
                match &xs[next] {
                    KindsTree::Atom(p) => match &ys[next] {
                        KindsTree::Atom(q) if p == q => {}
                        _ => return false,
                    },
                    KindsTree::Text(a) => match &ys[next] {
                        KindsTree::Text(b) if a == b => {}
                        _ => return false,
                    },
                    KindsTree::List(cs) => match &ys[next] {
                        KindsTree::List(ds) if cs.len() == ds.len() => pairs.push((cs, ds, 0)),
                        _ => return false,
                    },
                    KindsTree::Tuple(cs) => match &ys[next] {
                        KindsTree::Tuple(ds) if cs.len() == ds.len() => pairs.push((cs, ds, 0)),
                        _ => return false,
                    },
                    KindsTree::Record(ks, cs) => match &ys[next] {
                        KindsTree::Record(ls, ds) if cs.len() == ds.len() && ks == ls => {
                            pairs.push((cs, ds, 0))
                        }
                        _ => return false,
                    },
                    KindsTree::Map(ks, cs) => match &ys[next] {
                        KindsTree::Map(ls, ds) if cs.len() == ds.len() && ks == ls => {
                            pairs.push((cs, ds, 0))
                        }
                        _ => return false,
                    },
                    KindsTree::Array(es, xs_atoms) => match &ys[next] {
                        KindsTree::Array(fs, ys_atoms) if es == fs && xs_atoms == ys_atoms => {}
                        _ => return false,
                    },
                }
            }
        }
        true
    }

    /// Writes the elements `items` without recursion: a container opens when
    /// its frame is pushed, with the keys of a record or map written whole,
    /// and closes when the frame is finished.
    pub fn debug_items<A: fmt::Debug>(
        items: &[KindsTree<A>],
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let mut frames: Vec<Writing<'_, A>> = Vec::new();
        frames.push((KindsShape::Tuple, items, 0));
        while let Some((shape, items, next)) = frames.pop() {
            if next < items.len() {
                frames.push((shape, items, next + 1));
                if next > 0 {
                    f.write_str(", ")?;
                }
                match &items[next] {
                    KindsTree::Atom(atom) => fmt::Debug::fmt(atom, f)?,
                    KindsTree::Text(text) => fmt::Debug::fmt(text, f)?,
                    KindsTree::List(children) => {
                        f.write_str("List(")?;
                        frames.push((KindsShape::List, children, 0));
                    }
                    KindsTree::Tuple(children) => {
                        f.write_str("Tuple(")?;
                        frames.push((KindsShape::Tuple, children, 0));
                    }
                    KindsTree::Record(names, children) => {
                        f.write_str("Record(")?;
                        fmt::Debug::fmt(names, f)?;
                        f.write_str("; ")?;
                        frames.push((KindsShape::Record, children, 0));
                    }
                    KindsTree::Map(names, children) => {
                        f.write_str("Map(")?;
                        fmt::Debug::fmt(names, f)?;
                        f.write_str("; ")?;
                        frames.push((KindsShape::Map, children, 0));
                    }
                    KindsTree::Array(extents, atoms) => {
                        f.write_str("Array(")?;
                        fmt::Debug::fmt(extents, f)?;
                        f.write_str(", ")?;
                        fmt::Debug::fmt(atoms, f)?;
                        f.write_str(")")?;
                    }
                }
            } else if !frames.is_empty() {
                f.write_str(")")?;
            }
        }
        Ok(())
    }
}

/// A charged walk of the stored form of `collection_tree_kinds` whose frames
/// hold a borrowed slice of keys next to the borrowed slice of elements, so
/// that the entries of a record or map are visited with their keys: one loop
/// over one stack of such tuples.
pub mod collection_tree_keyed_frames {
    use crate::budget::{Budget, Exhausted};
    use crate::collection_tree_kinds::KindsTree;

    type Keyed<'a, A> = (&'a [String], &'a [KindsTree<A>], usize);

    /// The bytes of the keys of every entry below `items`, whose own keys
    /// are `keys`, charging one unit per step.
    pub fn key_bytes<A>(
        keys: &[String],
        items: &[KindsTree<A>],
        budget: &mut Budget,
    ) -> Result<usize, Exhausted> {
        let mut total = 0usize;
        let mut frames: Vec<Keyed<'_, A>> = Vec::new();
        frames.push((keys, items, 0));
        while let Some((keys, items, next)) = frames.pop() {
            budget.take(1)?;
            if next < items.len() {
                frames.push((keys, items, next + 1));
                if next < keys.len() {
                    total = total.saturating_add(keys[next].len());
                }
                match &items[next] {
                    KindsTree::Record(names, children) | KindsTree::Map(names, children) => {
                        frames.push((names, children, 0))
                    }
                    KindsTree::List(children) | KindsTree::Tuple(children) => {
                        frames.push((keys, children, 0))
                    }
                    _ => {}
                }
            }
        }
        Ok(total)
    }
}

/// The stored form of `collection_tree_kinds` instantiated over a value type
/// that holds it: the value type derives `Clone` and `PartialEq`, which call
/// the hand-written implementations of its list payload, and implements the
/// atom trait, whose cost and copy reach the generic traversals over the value
/// type again. Conversions into and out of the stored form move payloads
/// with `std::mem::take`, and the functions of the value layer call the
/// generic copy, equality and cost.
pub mod collection_value_instance {
    use crate::collection_hand_traits::{clone_items, eq_items};
    use crate::collection_tree_kinds::{
        self as tree, Atom, KindsContext, KindsCost, KindsFault, KindsTree, KindsTruth,
    };

    #[derive(Clone, PartialEq)]
    pub struct Txt(pub String);

    /// The elements of a list or tuple, in stored form.
    pub struct Seq(pub Vec<KindsTree<InstanceVal>>);

    impl Clone for Seq {
        fn clone(&self) -> Self {
            Seq(clone_items(&self.0))
        }
    }

    impl PartialEq for Seq {
        fn eq(&self, other: &Self) -> bool {
            eq_items(&self.0, &other.0)
        }
    }

    #[derive(Clone, PartialEq)]
    pub enum InstanceVal {
        Num(u64),
        Flag(bool),
        Text(Txt),
        List(Seq),
        Tuple(Seq),
    }

    /// Whether equal stored forms decide the answer for a value of this class.
    fn decided(value: &InstanceVal) -> bool {
        match value {
            InstanceVal::Num(_) | InstanceVal::Flag(_) => true,
            InstanceVal::Text(_) | InstanceVal::List(_) | InstanceVal::Tuple(_) => false,
        }
    }

    impl Atom for InstanceVal {
        fn cost(&self, context: &mut KindsContext) -> Result<KindsCost, KindsFault> {
            value_cost(self, context)
        }

        fn check(&self, context: &mut KindsContext) -> Result<(), KindsFault> {
            value_check(self, context)
        }

        fn same(&self, other: &Self, context: &mut KindsContext) -> Result<KindsTruth, KindsFault> {
            context.charge(1)?;
            if self == other {
                Ok(KindsTruth::True)
            } else if decided(self) && decided(other) {
                Ok(KindsTruth::False)
            } else {
                Ok(KindsTruth::Unknown)
            }
        }

        fn duplicate(&self) -> Self {
            self.clone()
        }
    }

    /// The cost of a value: the generic cost of the elements of a list or
    /// tuple and its overhead, and a fixed cost for the other classes.
    pub fn value_cost(
        value: &InstanceVal,
        context: &mut KindsContext,
    ) -> Result<KindsCost, KindsFault> {
        match value {
            InstanceVal::Num(_) | InstanceVal::Flag(_) => {
                context.charge(1)?;
                Ok(KindsCost { nodes: 1, bytes: 8 })
            }
            InstanceVal::Text(text) => match text.0.len().checked_add(8) {
                Some(bytes) => Ok(KindsCost { nodes: 1, bytes }),
                None => Err(KindsFault::Rejected),
            },
            InstanceVal::List(items) | InstanceVal::Tuple(items) => {
                match tree::cost_items(&items.0, context)? {
                    Some(cost) => match tree::add_cost(KindsCost { nodes: 1, bytes: 8 }, cost) {
                        Some(total) => Ok(total),
                        None => Err(KindsFault::Rejected),
                    },
                    None => Err(KindsFault::Rejected),
                }
            }
        }
    }

    pub fn value_check(value: &InstanceVal, context: &mut KindsContext) -> Result<(), KindsFault> {
        match value {
            InstanceVal::List(items) | InstanceVal::Tuple(items) => {
                tree::check_items(&items.0, context)
            }
            InstanceVal::Num(_) | InstanceVal::Flag(_) | InstanceVal::Text(_) => context.charge(1),
        }
    }

    /// The stored form of a value: the payload of a string, list or tuple,
    /// or the value itself as an atom.
    pub fn into_tree(mut value: InstanceVal) -> KindsTree<InstanceVal> {
        let moved = match &mut value {
            InstanceVal::Text(text) => Some(KindsTree::Text(std::mem::take(&mut text.0))),
            InstanceVal::List(items) => Some(KindsTree::List(std::mem::take(&mut items.0))),
            InstanceVal::Tuple(items) => Some(KindsTree::Tuple(std::mem::take(&mut items.0))),
            InstanceVal::Num(_) | InstanceVal::Flag(_) => None,
        };
        match moved {
            Some(tree) => tree,
            None => KindsTree::Atom(value),
        }
    }

    /// The value of a stored form; records, maps and arrays have no variant
    /// in this value type.
    pub fn from_tree(mut tree: KindsTree<InstanceVal>) -> Option<InstanceVal> {
        match &mut tree {
            KindsTree::Atom(atom) => Some(std::mem::replace(atom, InstanceVal::Flag(false))),
            KindsTree::Text(text) => Some(InstanceVal::Text(Txt(std::mem::take(text)))),
            KindsTree::List(items) => Some(InstanceVal::List(Seq(std::mem::take(items)))),
            KindsTree::Tuple(items) => Some(InstanceVal::Tuple(Seq(std::mem::take(items)))),
            KindsTree::Record(_, _) | KindsTree::Map(_, _) | KindsTree::Array(_, _) => None,
        }
    }

    /// Appends a value to the elements of a list or tuple being built.
    pub fn push_value(items: &mut Seq, value: InstanceVal) {
        items.0.push(into_tree(value));
    }

    /// A charged copy: lists and tuples through the generic copy.
    pub fn copy_value(
        value: &InstanceVal,
        context: &mut KindsContext,
    ) -> Result<InstanceVal, KindsFault> {
        match value {
            InstanceVal::List(items) => {
                Ok(InstanceVal::List(Seq(tree::copy_items(&items.0, context)?)))
            }
            InstanceVal::Tuple(items) => Ok(InstanceVal::Tuple(Seq(tree::copy_items(
                &items.0, context,
            )?))),
            InstanceVal::Num(_) | InstanceVal::Flag(_) | InstanceVal::Text(_) => {
                Ok(value.duplicate())
            }
        }
    }

    /// Element `position` of a list or tuple, copied through the generic
    /// copy of one element; the caller has checked the kind and the range.
    pub fn element(
        value: &InstanceVal,
        position: usize,
        context: &mut KindsContext,
    ) -> Result<Option<InstanceVal>, KindsFault> {
        match value {
            InstanceVal::List(items) | InstanceVal::Tuple(items) => {
                let mut copies =
                    tree::copy_items(std::slice::from_ref(&items.0[position]), context)?;
                match copies.pop() {
                    Some(copy) => Ok(from_tree(copy)),
                    None => Ok(None),
                }
            }
            InstanceVal::Num(_) | InstanceVal::Flag(_) | InstanceVal::Text(_) => Ok(None),
        }
    }

    /// Three-valued equality: lists and tuples through the generic equality,
    /// values of different kinds false, and atoms by their test.
    pub fn equal_values(
        left: &InstanceVal,
        right: &InstanceVal,
        context: &mut KindsContext,
    ) -> Result<KindsTruth, KindsFault> {
        match left {
            InstanceVal::List(a) => match right {
                InstanceVal::List(b) => tree::equal_items(&a.0, &b.0, context),
                _ => Ok(KindsTruth::False),
            },
            InstanceVal::Tuple(a) => match right {
                InstanceVal::Tuple(b) => tree::equal_items(&a.0, &b.0, context),
                _ => Ok(KindsTruth::False),
            },
            InstanceVal::Text(a) => match right {
                InstanceVal::Text(b) => {
                    context.charge(1)?;
                    if a == b {
                        Ok(KindsTruth::True)
                    } else {
                        Ok(KindsTruth::False)
                    }
                }
                _ => Ok(KindsTruth::False),
            },
            InstanceVal::Num(_) | InstanceVal::Flag(_) => match right {
                InstanceVal::Num(_) | InstanceVal::Flag(_) => left.same(right, context),
                _ => Ok(KindsTruth::False),
            },
        }
    }
}

/// Nested iterators as copyable stages in one vector, linked by the positions
/// of their inputs: ranges, maps, filters and zips. A step walks from the
/// root to the input it consults and back over an explicit stack of
/// positions, in one loop whose iteration handles one stage by a `match`. A
/// stage's new state is built in a local and assigned to its position. Maps,
/// filters and zips hold the identity of a function rather than a closure and
/// hand the call back to a driver, which keeps the stack and resumes the step
/// with the answer. Elements are handles of values that the driver holds.
pub mod iterator_arena {
    use crate::budget::{Budget, Exhausted};

    #[derive(Clone, Copy)]
    pub enum ArenaStage {
        /// The integers from `next` while they stay below `end`.
        Range {
            next: u64,
            end: u64,
        },
        /// The result of calling `function` on every element of `source`.
        Map {
            source: usize,
            function: u32,
        },
        /// The elements of `source` for which `function` answers true.
        Filter {
            source: usize,
            function: u32,
        },
        /// Pairs of one element of `first` and one of `second`; every step
        /// consults one input, and `held` is the element taken from `first`.
        Zip {
            first: usize,
            second: usize,
            held: Option<u64>,
        },
        Finished,
    }

    #[derive(Clone, Copy)]
    pub enum ArenaEvent {
        Finished,
        Skipped,
        Yielded(u64),
        /// The driver calls the function on the element and resumes with
        /// its result as the element yielded.
        Apply(u32, u64),
        /// The driver calls the predicate on the element and resumes with
        /// the element or a skip.
        Test(u32, u64),
        /// The driver builds the pair and resumes with its handle.
        Pair(u64, u64),
    }

    /// Whether a step goes down to the stage it pops or carries the event of
    /// an input up to it.
    #[derive(Clone, Copy)]
    pub enum ArenaFlow {
        Down,
        Up(ArenaEvent),
    }

    /// What handling one stage gives: the flow of the next iteration, or an
    /// event for the driver.
    enum ArenaVisit {
        Continue(ArenaFlow),
        Hand(ArenaEvent),
    }

    /// The calls that the driver makes for the stages.
    pub trait ArenaCalls {
        fn apply(
            &mut self,
            function: u32,
            element: u64,
            budget: &mut Budget,
        ) -> Result<u64, Exhausted>;
        fn test(
            &mut self,
            function: u32,
            element: u64,
            budget: &mut Budget,
        ) -> Result<bool, Exhausted>;
        fn pair(&mut self, first: u64, second: u64, budget: &mut Budget) -> Result<u64, Exhausted>;
    }

    /// Advances the stages on `path` until the root has an event or a stage
    /// hands a call to the driver, charging one unit per stage visited.
    pub fn step(
        stages: &mut [ArenaStage],
        path: &mut Vec<usize>,
        flow: ArenaFlow,
        budget: &mut Budget,
    ) -> Result<ArenaEvent, Exhausted> {
        let mut flow = flow;
        while let Some(index) = path.pop() {
            budget.take(1)?;
            match visit(stages, path, index, flow) {
                ArenaVisit::Continue(next) => flow = next,
                ArenaVisit::Hand(event) => return Ok(event),
            }
        }
        match flow {
            ArenaFlow::Up(event) => Ok(event),
            ArenaFlow::Down => Ok(ArenaEvent::Finished),
        }
    }

    /// Handles the stage at `index` for one iteration of `step`.
    fn visit(
        stages: &mut [ArenaStage],
        path: &mut Vec<usize>,
        index: usize,
        flow: ArenaFlow,
    ) -> ArenaVisit {
        let stage = stages[index];
        match stage {
            ArenaStage::Range { next, end } => {
                if next < end {
                    let advanced = ArenaStage::Range {
                        next: next + 1,
                        end,
                    };
                    stages[index] = advanced;
                    ArenaVisit::Continue(ArenaFlow::Up(ArenaEvent::Yielded(next)))
                } else {
                    ArenaVisit::Continue(ArenaFlow::Up(ArenaEvent::Finished))
                }
            }
            ArenaStage::Map { source, function } => match flow {
                ArenaFlow::Down => {
                    path.push(index);
                    path.push(source);
                    ArenaVisit::Continue(ArenaFlow::Down)
                }
                ArenaFlow::Up(ArenaEvent::Yielded(element)) => {
                    ArenaVisit::Hand(ArenaEvent::Apply(function, element))
                }
                ArenaFlow::Up(event) => ArenaVisit::Continue(ArenaFlow::Up(event)),
            },
            ArenaStage::Filter { source, function } => match flow {
                ArenaFlow::Down => {
                    path.push(index);
                    path.push(source);
                    ArenaVisit::Continue(ArenaFlow::Down)
                }
                ArenaFlow::Up(ArenaEvent::Yielded(element)) => {
                    ArenaVisit::Hand(ArenaEvent::Test(function, element))
                }
                ArenaFlow::Up(event) => ArenaVisit::Continue(ArenaFlow::Up(event)),
            },
            ArenaStage::Zip {
                first,
                second,
                held,
            } => match flow {
                ArenaFlow::Down => {
                    path.push(index);
                    match held {
                        None => path.push(first),
                        Some(_) => path.push(second),
                    }
                    ArenaVisit::Continue(ArenaFlow::Down)
                }
                ArenaFlow::Up(ArenaEvent::Yielded(element)) => match held {
                    None => {
                        let taken = ArenaStage::Zip {
                            first,
                            second,
                            held: Some(element),
                        };
                        stages[index] = taken;
                        ArenaVisit::Continue(ArenaFlow::Up(ArenaEvent::Skipped))
                    }
                    Some(left) => {
                        let emptied = ArenaStage::Zip {
                            first,
                            second,
                            held: None,
                        };
                        stages[index] = emptied;
                        ArenaVisit::Hand(ArenaEvent::Pair(left, element))
                    }
                },
                ArenaFlow::Up(ArenaEvent::Finished) => {
                    stages[index] = ArenaStage::Finished;
                    ArenaVisit::Continue(ArenaFlow::Up(ArenaEvent::Finished))
                }
                ArenaFlow::Up(event) => ArenaVisit::Continue(ArenaFlow::Up(event)),
            },
            ArenaStage::Finished => ArenaVisit::Continue(ArenaFlow::Up(ArenaEvent::Finished)),
        }
    }

    /// Collects the elements of the iterator at `root`, making the calls
    /// that its stages hand back.
    pub fn collect<C: ArenaCalls>(
        stages: &mut [ArenaStage],
        root: usize,
        calls: &mut C,
        budget: &mut Budget,
    ) -> Result<Vec<u64>, Exhausted> {
        let mut elements = Vec::new();
        let mut path = Vec::new();
        path.push(root);
        let mut flow = ArenaFlow::Down;
        loop {
            match step(stages, &mut path, flow, budget)? {
                ArenaEvent::Finished => return Ok(elements),
                ArenaEvent::Skipped => {
                    path.push(root);
                    flow = ArenaFlow::Down;
                }
                ArenaEvent::Yielded(element) => {
                    elements.push(element);
                    path.push(root);
                    flow = ArenaFlow::Down;
                }
                ArenaEvent::Apply(function, element) => {
                    let result = calls.apply(function, element, budget)?;
                    flow = ArenaFlow::Up(ArenaEvent::Yielded(result));
                }
                ArenaEvent::Test(function, element) => {
                    flow = if calls.test(function, element, budget)? {
                        ArenaFlow::Up(ArenaEvent::Yielded(element))
                    } else {
                        ArenaFlow::Up(ArenaEvent::Skipped)
                    };
                }
                ArenaEvent::Pair(first, second) => {
                    let pair = calls.pair(first, second, budget)?;
                    flow = ArenaFlow::Up(ArenaEvent::Yielded(pair));
                }
            }
        }
    }
}

/// The iterators of `iterator_arena` nested through `Box`. A step moves the
/// input it consults out of its parent with `std::mem::replace`, and the
/// parent onto an owned stack, walks down to a range and back up, putting
/// every input back into its parent; the driver keeps the stack while a call
/// is pending. `Drop` releases nested iterators through an owned stack.
pub mod iterator_owned_stack {
    use crate::budget::{Budget, Exhausted};

    pub enum OwnedIter {
        Range {
            next: u64,
            end: u64,
        },
        Map {
            source: Box<OwnedIter>,
            function: u32,
        },
        Filter {
            source: Box<OwnedIter>,
            function: u32,
        },
        Zip {
            first: Box<OwnedIter>,
            second: Box<OwnedIter>,
            held: Option<u64>,
        },
        Finished,
    }

    #[derive(Clone, Copy)]
    pub enum OwnedEvent {
        Finished,
        Skipped,
        Yielded(u64),
        Apply(u32, u64),
        Test(u32, u64),
        Pair(u64, u64),
    }

    #[derive(Clone, Copy)]
    pub enum OwnedFlow {
        Down,
        Up(OwnedEvent),
    }

    enum OwnedNext {
        Carry(OwnedEvent),
        Hand(OwnedEvent),
    }

    /// The calls that the driver makes for the iterators.
    pub trait OwnedCalls {
        fn apply(
            &mut self,
            function: u32,
            element: u64,
            budget: &mut Budget,
        ) -> Result<u64, Exhausted>;
        fn test(
            &mut self,
            function: u32,
            element: u64,
            budget: &mut Budget,
        ) -> Result<bool, Exhausted>;
        fn pair(&mut self, first: u64, second: u64, budget: &mut Budget) -> Result<u64, Exhausted>;
    }

    /// The iterator being stepped and the ancestors moved out of the chain
    /// above it, innermost last, each without the input on the path.
    pub struct OwnedWalk {
        pub current: OwnedIter,
        pub parents: Vec<OwnedIter>,
    }

    impl Drop for OwnedIter {
        fn drop(&mut self) {
            let mut stack = Vec::new();
            detach_all(self, &mut stack);
            while let Some(mut iterator) = stack.pop() {
                detach_all(&mut iterator, &mut stack);
            }
        }
    }

    /// Moves every input of `iterator` onto `stack`, leaving finished ones.
    fn detach_all(iterator: &mut OwnedIter, stack: &mut Vec<OwnedIter>) {
        match iterator {
            OwnedIter::Map { source, .. } | OwnedIter::Filter { source, .. } => {
                stack.push(std::mem::replace(&mut **source, OwnedIter::Finished))
            }
            OwnedIter::Zip { first, second, .. } => {
                stack.push(std::mem::replace(&mut **first, OwnedIter::Finished));
                stack.push(std::mem::replace(&mut **second, OwnedIter::Finished));
            }
            OwnedIter::Range { .. } | OwnedIter::Finished => {}
        }
    }

    /// Moves the input that `iterator` consults next out of it, if it has
    /// inputs.
    fn detach(iterator: &mut OwnedIter) -> Option<OwnedIter> {
        match iterator {
            OwnedIter::Map { source, .. } | OwnedIter::Filter { source, .. } => {
                Some(std::mem::replace(&mut **source, OwnedIter::Finished))
            }
            OwnedIter::Zip {
                first,
                second,
                held,
            } => match held {
                None => Some(std::mem::replace(&mut **first, OwnedIter::Finished)),
                Some(_) => Some(std::mem::replace(&mut **second, OwnedIter::Finished)),
            },
            OwnedIter::Range { .. } | OwnedIter::Finished => None,
        }
    }

    /// The event of an iterator without inputs.
    fn leaf(iterator: &mut OwnedIter) -> OwnedEvent {
        match iterator {
            OwnedIter::Range { next, end } => {
                if *next < *end {
                    let element = *next;
                    let advanced = element + 1;
                    *next = advanced;
                    OwnedEvent::Yielded(element)
                } else {
                    OwnedEvent::Finished
                }
            }
            _ => OwnedEvent::Finished,
        }
    }

    /// Goes down one level: moves the consulted input out of the current
    /// iterator and the iterator onto the parents, or takes the event of a
    /// range.
    fn descend(walk: &mut OwnedWalk) -> OwnedFlow {
        match detach(&mut walk.current) {
            Some(input) => {
                let parent = std::mem::replace(&mut walk.current, input);
                walk.parents.push(parent);
                OwnedFlow::Down
            }
            None => OwnedFlow::Up(leaf(&mut walk.current)),
        }
    }

    /// Puts `input` back into `parent` and handles the event it produced.
    fn ascend(parent: &mut OwnedIter, input: OwnedIter, event: OwnedEvent) -> OwnedNext {
        match parent {
            OwnedIter::Map { source, function } => {
                **source = input;
                match event {
                    OwnedEvent::Yielded(element) => {
                        OwnedNext::Hand(OwnedEvent::Apply(*function, element))
                    }
                    other => OwnedNext::Carry(other),
                }
            }
            OwnedIter::Filter { source, function } => {
                **source = input;
                match event {
                    OwnedEvent::Yielded(element) => {
                        OwnedNext::Hand(OwnedEvent::Test(*function, element))
                    }
                    other => OwnedNext::Carry(other),
                }
            }
            OwnedIter::Zip {
                first,
                second,
                held,
            } => match *held {
                None => {
                    **first = input;
                    match event {
                        OwnedEvent::Yielded(element) => {
                            *held = Some(element);
                            OwnedNext::Carry(OwnedEvent::Skipped)
                        }
                        other => OwnedNext::Carry(other),
                    }
                }
                Some(left) => {
                    **second = input;
                    match event {
                        OwnedEvent::Yielded(element) => {
                            *held = None;
                            OwnedNext::Hand(OwnedEvent::Pair(left, element))
                        }
                        other => OwnedNext::Carry(other),
                    }
                }
            },
            OwnedIter::Range { .. } | OwnedIter::Finished => OwnedNext::Carry(event),
        }
    }

    /// Advances the walk until the root has an event or an iterator hands a
    /// call to the driver, charging one unit per level visited.
    pub fn step(
        walk: &mut OwnedWalk,
        flow: OwnedFlow,
        budget: &mut Budget,
    ) -> Result<OwnedEvent, Exhausted> {
        let mut flow = flow;
        loop {
            budget.take(1)?;
            match flow {
                OwnedFlow::Down => flow = descend(walk),
                OwnedFlow::Up(event) => match walk.parents.pop() {
                    None => return Ok(event),
                    Some(parent) => {
                        let input = std::mem::replace(&mut walk.current, parent);
                        match ascend(&mut walk.current, input, event) {
                            OwnedNext::Carry(next) => flow = OwnedFlow::Up(next),
                            OwnedNext::Hand(request) => return Ok(request),
                        }
                    }
                },
            }
        }
    }

    /// Collects the elements of `root`, making the calls that its iterators
    /// hand back.
    pub fn collect<C: OwnedCalls>(
        root: OwnedIter,
        calls: &mut C,
        budget: &mut Budget,
    ) -> Result<Vec<u64>, Exhausted> {
        let mut elements = Vec::new();
        let mut walk = OwnedWalk {
            current: root,
            parents: Vec::new(),
        };
        let mut flow = OwnedFlow::Down;
        loop {
            match step(&mut walk, flow, budget)? {
                OwnedEvent::Finished => return Ok(elements),
                OwnedEvent::Skipped => flow = OwnedFlow::Down,
                OwnedEvent::Yielded(element) => {
                    elements.push(element);
                    flow = OwnedFlow::Down;
                }
                OwnedEvent::Apply(function, element) => {
                    let result = calls.apply(function, element, budget)?;
                    flow = OwnedFlow::Up(OwnedEvent::Yielded(result));
                }
                OwnedEvent::Test(function, element) => {
                    flow = if calls.test(function, element, budget)? {
                        OwnedFlow::Up(OwnedEvent::Yielded(element))
                    } else {
                        OwnedFlow::Up(OwnedEvent::Skipped)
                    };
                }
                OwnedEvent::Pair(first, second) => {
                    let pair = calls.pair(first, second, budget)?;
                    flow = OwnedFlow::Up(OwnedEvent::Yielded(pair));
                }
            }
        }
    }
}

/// A storage measure summed in a `for` loop over a generic
/// `impl IntoIterator` parameter of borrowed items, as the library's
/// `polynomial_cost` sums the measures of the polynomials it is given, and a
/// caller that passes it an array.
pub mod generic_into_iterator_loop {
    use crate::budget::{Budget, Exhausted};

    pub struct Item {
        pub weight: u32,
    }

    pub fn total<'a>(
        items: impl IntoIterator<Item = &'a Item>,
        budget: &mut Budget,
    ) -> Result<u32, Exhausted> {
        let mut sum = 0u32;
        for item in items {
            budget.take(1)?;
            sum = sum.saturating_add(item.weight);
        }
        Ok(sum)
    }

    pub fn pair_total(a: &Item, b: &Item, budget: &mut Budget) -> Result<u32, Exhausted> {
        total([a, b], budget)
    }
}

/// The measure of `generic_into_iterator_loop` as a non-generic step for one
/// item, which a caller calls once per item in order, as
/// `add_polynomial_cost` is called.
pub mod generic_into_iterator_step {
    use crate::budget::{Budget, Exhausted};

    pub struct Item {
        pub weight: u32,
    }

    pub fn add_weight(sum: u32, item: &Item, budget: &mut Budget) -> Result<u32, Exhausted> {
        budget.take(1)?;
        Ok(sum.saturating_add(item.weight))
    }

    pub fn pair_total(a: &Item, b: &Item, budget: &mut Budget) -> Result<u32, Exhausted> {
        let sum = add_weight(0, a, budget)?;
        add_weight(sum, b, budget)
    }
}

/// The reduction of a number-field element as two moving joins: an `if` on a
/// comparison of the variable with a string literal that keeps an owned
/// sparse polynomial or rebinds it with `?`, then a flag computed by a
/// `match` on the degree and an `if` on the flag whose arms join before
/// further code, one of which moves the polynomial while the other borrows
/// it for a division with `?` and keeps the second component of the quotient
/// pair. This is `NumberField::reduce` with its `Option::is_some_and` written
/// as a `match`.
pub mod moving_if_join {
    use std::collections::BTreeMap;

    use crate::budget::{Budget, Exhausted};

    #[derive(Clone)]
    pub struct Sparse {
        pub variable: String,
        pub terms: BTreeMap<u32, u32>,
    }

    impl Sparse {
        pub fn variable(&self) -> &str {
            &self.variable
        }
    }

    // A `match` rather than `Option::map`, as `Polynomial::degree` is written.
    #[allow(clippy::manual_map)]
    fn degree(p: &Sparse) -> Option<u32> {
        match p.terms.last_key_value() {
            Some((&degree, _)) => Some(degree),
            None => None,
        }
    }

    fn rebind(p: &Sparse, variable: &str, budget: &mut Budget) -> Result<Sparse, Exhausted> {
        budget.take(1)?;
        Ok(Sparse {
            variable: variable.to_owned(),
            terms: p.terms.clone(),
        })
    }

    fn div_rem(p: &Sparse, budget: &mut Budget) -> Result<(Sparse, Sparse), Exhausted> {
        budget.take(1)?;
        Ok((p.clone(), p.clone()))
    }

    pub fn reduce(p: Sparse, bound: u32, budget: &mut Budget) -> Result<Sparse, Exhausted> {
        budget.take(1)?;
        let p = if p.variable() == "a" {
            p
        } else {
            rebind(&p, "a", budget)?
        };
        let reducible = match degree(&p) {
            Some(n) => n >= bound,
            None => false,
        };
        let result = if reducible { div_rem(&p, budget)?.1 } else { p };
        budget.take(1)?;
        Ok(result)
    }
}

/// The reduction of `moving_if_join` with the second branch in a helper
/// whose arms both return, one of them early, as `NumberField::reduce_degree`
/// does; the first join stays in the reduction.
pub mod moving_if_helper {
    use std::collections::BTreeMap;

    use crate::budget::{Budget, Exhausted};

    #[derive(Clone)]
    pub struct Sparse {
        pub variable: String,
        pub terms: BTreeMap<u32, u32>,
    }

    impl Sparse {
        pub fn variable(&self) -> &str {
            &self.variable
        }
    }

    // A `match` rather than `Option::map`, as `Polynomial::degree` is written.
    #[allow(clippy::manual_map)]
    fn degree(p: &Sparse) -> Option<u32> {
        match p.terms.last_key_value() {
            Some((&degree, _)) => Some(degree),
            None => None,
        }
    }

    fn rebind(p: &Sparse, variable: &str, budget: &mut Budget) -> Result<Sparse, Exhausted> {
        budget.take(1)?;
        Ok(Sparse {
            variable: variable.to_owned(),
            terms: p.terms.clone(),
        })
    }

    fn div_rem(p: &Sparse, budget: &mut Budget) -> Result<(Sparse, Sparse), Exhausted> {
        budget.take(1)?;
        Ok((p.clone(), p.clone()))
    }

    fn reduce_degree(p: Sparse, bound: u32, budget: &mut Budget) -> Result<Sparse, Exhausted> {
        let reducible = match degree(&p) {
            Some(n) => n >= bound,
            None => false,
        };
        if !reducible {
            return Ok(p);
        }
        Ok(div_rem(&p, budget)?.1)
    }

    pub fn reduce(p: Sparse, bound: u32, budget: &mut Budget) -> Result<Sparse, Exhausted> {
        budget.take(1)?;
        let p = if p.variable() == "a" {
            p
        } else {
            rebind(&p, "a", budget)?
        };
        let result = reduce_degree(p, bound, budget)?;
        budget.take(1)?;
        Ok(result)
    }
}

/// A search over a slice of sparse polynomials in an index loop that charges
/// with `?`, unwraps the leading term of the current polynomial with
/// `last_key_value().unwrap()` and returns the position of the first one
/// whose leading degree divides a given one, as the multivariate division
/// finds its first divisor.
pub mod unwrap_in_loop {
    use std::collections::BTreeMap;

    use crate::budget::{Budget, Exhausted};

    pub struct Sparse {
        pub terms: BTreeMap<u32, u32>,
    }

    pub fn first_divisor(
        degree: u32,
        divisors: &[Sparse],
        budget: &mut Budget,
    ) -> Result<Option<usize>, Exhausted> {
        let mut index = 0;
        while index < divisors.len() {
            budget.take(1)?;
            let (&leading, _) = divisors[index].terms.last_key_value().unwrap();
            if leading <= degree {
                return Ok(Some(index));
            }
            index += 1;
        }
        Ok(None)
    }
}

/// The search of `unwrap_in_loop` with the unwrap and the test of the leading
/// degree in a loopless helper that the loop calls.
pub mod unwrap_in_helper {
    use std::collections::BTreeMap;

    use crate::budget::{Budget, Exhausted};

    pub struct Sparse {
        pub terms: BTreeMap<u32, u32>,
    }

    fn leading_divides(degree: u32, divisor: &Sparse) -> bool {
        let (&leading, _) = divisor.terms.last_key_value().unwrap();
        leading <= degree
    }

    pub fn first_divisor(
        degree: u32,
        divisors: &[Sparse],
        budget: &mut Budget,
    ) -> Result<Option<usize>, Exhausted> {
        let mut index = 0;
        while index < divisors.len() {
            budget.take(1)?;
            if leading_divides(degree, &divisors[index]) {
                return Ok(Some(index));
            }
            index += 1;
        }
        Ok(None)
    }
}

/// Ordered division and the factor loop of the multivariate GCD in the forms
/// of the library. A `while let` borrows the last entry of a map in its
/// condition, copies its key and clones its value, passes them, with `&mut`
/// to the working map and to a result structure, to a loopless step helper
/// called with `?`, then makes two further checks with `?`. The helper
/// matches on the result of a search called with `?`: one arm assigns an
/// element of a vector that the structure holds from a `?` call that reads
/// that element and replaces the working map through its `&mut` with a `?`
/// call that reads it, the other moves the entry from the working map into a
/// map of the structure. A counter loop charges with `?` and runs an `if
/// let` on a `?` call whose body assigns its payload to one `&mut` value and
/// a `?` call to another, and whose `else` breaks; an index loop calls it
/// with `?` for each element of a slice.
pub mod division_walk {
    use std::collections::BTreeMap;

    use crate::budget::{Budget, Exhausted};

    /// The quotients by each divisor and the terms moved to the remainder.
    pub struct Division {
        pub quotients: Vec<Vec<u32>>,
        pub remainder: BTreeMap<u32, Vec<u32>>,
    }

    /// A factor and its multiplicity.
    pub struct Factor {
        pub value: u32,
        pub multiplicity: u32,
    }

    pub fn walk(
        mut work: BTreeMap<u32, Vec<u32>>,
        divisors: &[u32],
        mut result: Division,
        budget: &mut Budget,
    ) -> Result<Division, Exhausted> {
        while let Some((degree, value)) = work.last_key_value() {
            let degree = *degree;
            let value = value.clone();
            step(&mut work, &mut result, degree, value, divisors, budget)?;
            check(&result.remainder, budget)?;
            check(&work, budget)?;
        }
        Ok(result)
    }

    fn step(
        work: &mut BTreeMap<u32, Vec<u32>>,
        result: &mut Division,
        degree: u32,
        value: Vec<u32>,
        divisors: &[u32],
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        match first_divisor(degree, divisors, budget)? {
            Some(index) => {
                result.quotients[index] = extend(&result.quotients[index], degree, budget)?;
                *work = reduce(work, degree, budget)?;
                Ok(())
            }
            None => {
                work.remove(&degree);
                result.remainder.insert(degree, value);
                Ok(())
            }
        }
    }

    fn first_divisor(
        degree: u32,
        divisors: &[u32],
        budget: &mut Budget,
    ) -> Result<Option<usize>, Exhausted> {
        let mut index = 0;
        while index < divisors.len() {
            budget.take(1)?;
            if divisors[index] <= degree {
                return Ok(Some(index));
            }
            index += 1;
        }
        Ok(None)
    }

    fn extend(values: &[u32], value: u32, budget: &mut Budget) -> Result<Vec<u32>, Exhausted> {
        budget.take(1)?;
        let mut next = values.to_vec();
        next.push(value);
        Ok(next)
    }

    fn reduce(
        work: &BTreeMap<u32, Vec<u32>>,
        degree: u32,
        budget: &mut Budget,
    ) -> Result<BTreeMap<u32, Vec<u32>>, Exhausted> {
        budget.take(1)?;
        let mut next = work.clone();
        next.remove(&degree);
        Ok(next)
    }

    fn check(terms: &BTreeMap<u32, Vec<u32>>, budget: &mut Budget) -> Result<(), Exhausted> {
        budget.take(terms.len() as u64)
    }

    pub fn common_factors(
        factors: &[Factor],
        mut remaining: Vec<u32>,
        mut answer: Vec<u32>,
        budget: &mut Budget,
    ) -> Result<Vec<u32>, Exhausted> {
        let mut index = 0;
        while index < factors.len() {
            divide_out(&factors[index], &mut remaining, &mut answer, budget)?;
            index += 1;
        }
        Ok(answer)
    }

    fn divide_out(
        factor: &Factor,
        remaining: &mut Vec<u32>,
        answer: &mut Vec<u32>,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        let count = factor.multiplicity;
        let mut done = 0;
        while done < count {
            budget.take(1)?;
            if let Some(quotient) = exact(remaining, factor.value, budget)? {
                *remaining = quotient;
                *answer = extend(answer, factor.value, budget)?;
            } else {
                break;
            }
            done += 1;
        }
        Ok(())
    }

    fn exact(
        values: &[u32],
        divisor: u32,
        budget: &mut Budget,
    ) -> Result<Option<Vec<u32>>, Exhausted> {
        budget.take(1)?;
        if divisor as usize <= values.len() {
            Ok(Some(values.to_vec()))
        } else {
            Ok(None)
        }
    }
}

/// A function whose body a `cfg` chooses, the shape that rule 7 of the
/// provable subset forbids: each configuration compiles a different body,
/// with a helper of its own. The extraction sets no `cfg`, so it translates
/// the helper of the default configuration alone.
pub mod cfg_shape {
    /// The pages that one block entry maps.
    #[cfg(board = "pi5")]
    const BLOCK_PAGES: u64 = 512;

    /// The block entries that map `count` pages from page `first`.
    #[cfg(board = "pi5")]
    fn map_blocks(first: u64, count: u64) -> u64 {
        let mut entries = 0;
        let mut page = first;
        while page - first < count {
            entries += 1;
            page += BLOCK_PAGES;
        }
        entries
    }

    /// The page entries that map `count` pages from page `first`.
    #[cfg(not(board = "pi5"))]
    fn map_pages(first: u64, count: u64) -> u64 {
        let mut entries = 0;
        let mut page = first;
        while page - first < count {
            entries += 1;
            page += 1;
        }
        entries
    }

    pub fn map_ram(first: u64, count: u64) -> u64 {
        #[cfg(board = "pi5")]
        return map_blocks(first, count);
        #[cfg(not(board = "pi5"))]
        return map_pages(first, count);
    }
}

/// A record over an array whose length is a const generic parameter, as a
/// budget ledger with one charge per slot: a sum over the array in an index
/// loop bounded by the parameter, and a checked charge of one slot.
pub mod const_generic {
    pub struct Exhausted;

    pub struct Ledger<const N: usize> {
        pub charges: [u64; N],
    }

    impl<const N: usize> Ledger<N> {
        pub fn total(&self) -> u64 {
            let mut total = 0;
            let mut index = 0;
            while index < N {
                total += self.charges[index];
                index += 1;
            }
            total
        }

        pub fn charge(&mut self, slot: usize, amount: u64) -> Result<(), Exhausted> {
            match self.charges[slot].checked_add(amount) {
                Some(charged) => {
                    self.charges[slot] = charged;
                    Ok(())
                }
                None => Err(Exhausted),
            }
        }
    }
}

/// Item R1 of the provable subset: a function item whose signature has a
/// late-bound lifetime, `Option::is_some`, passed as a value to
/// `Iterator::any`.
pub mod r1_function_item_value {
    #[derive(Clone, Copy)]
    pub struct Activation {
        pub key: u64,
        pub legacy: bool,
    }

    pub fn any_active(active: &[Option<Activation>]) -> bool {
        active.iter().any(Option::is_some)
    }
}

/// Item R2 of the provable subset: `Iterator::any` with a closure.
pub mod r2_iterator_any {
    pub struct Thread {
        pub process: u64,
        pub alive: bool,
    }

    pub fn has_survivor(threads: &[Thread], process: u64) -> bool {
        threads
            .iter()
            .any(|thread| thread.process == process && thread.alive)
    }
}

/// Item R3 of the provable subset: a `for` loop over `Iterator::flatten`,
/// which skips the empty slots of a table.
pub mod r3_iterator_flatten {
    #[derive(Clone, Copy)]
    pub struct Activation {
        pub key: u64,
        pub legacy: bool,
    }

    pub fn holds_legacy(active: &[Option<Activation>]) -> bool {
        for activation in active.iter().flatten() {
            if activation.legacy {
                return true;
            }
        }
        false
    }
}

/// Item R4 of the provable subset: a closure given to `Result::map_err`,
/// after a search in an index loop that returns from inside the loop.
pub mod r4_closure_callback {
    pub enum Error {
        InvalidState,
        Missing,
    }

    pub struct Pool {
        pub processes: [u64; 4],
    }

    impl Pool {
        pub fn process_index(&self, process: u64) -> Result<usize, Error> {
            let mut index = 0;
            while index < self.processes.len() {
                if self.processes[index] == process {
                    return Ok(index);
                }
                index += 1;
            }
            Err(Error::Missing)
        }
    }

    pub fn owner(pool: &Pool, process: u64) -> Result<usize, Error> {
        pool.process_index(process).map_err(|_| Error::InvalidState)
    }
}

/// Item R5 of the provable subset, the reduced stop path: a mutable borrow
/// of a table entry held across an early return and a write to another
/// field of `self`, then a conditional update of an entry of another table
/// through a mutable borrow inside a branch whose arms meet again before
/// further code. The tables are fixed arrays.
pub mod r5_stop_path_borrow_join {
    #[derive(Clone, Copy, PartialEq)]
    pub enum ThreadState {
        Running,
        Dead,
    }

    #[derive(Clone, Copy, PartialEq)]
    pub enum ProcessState {
        Alive,
        Dying,
    }

    #[derive(Clone, Copy)]
    pub enum ExitReason {
        Exited,
        Killed,
    }

    pub struct ThreadEntry {
        pub state: ThreadState,
        pub process: usize,
        pub exit: Option<ExitReason>,
    }

    pub struct ProcessEntry {
        pub state: ProcessState,
    }

    pub struct Pool {
        pub threads: [ThreadEntry; 4],
        pub processes: [ProcessEntry; 4],
        pub stopped: u64,
    }

    impl Pool {
        fn has_survivor(&self, process: usize) -> bool {
            let mut index = 0;
            while index < self.threads.len() {
                if self.threads[index].process == process
                    && self.threads[index].state == ThreadState::Running
                {
                    return true;
                }
                index += 1;
            }
            false
        }

        fn finish_thread(&mut self, index: usize) {
            self.threads[index].state = ThreadState::Dead;
        }

        pub fn stop_thread(&mut self, index: usize, reason: ExitReason) {
            let entry = &mut self.threads[index];
            if entry.state == ThreadState::Dead {
                return;
            }
            entry.exit = Some(reason);
            self.stopped += 1;
            let process = entry.process;
            if !self.has_survivor(process) {
                let owner = &mut self.processes[process];
                if owner.state == ProcessState::Alive {
                    owner.state = ProcessState::Dying;
                }
            }
            self.finish_thread(index);
        }
    }
}

/// Item R6 of the provable subset: two modules that each define an
/// enumeration `Error`. The case extracts each module on its own and builds
/// a Lean module that imports the definitions of both.
pub mod r6_same_enum_name {
    pub mod objects {
        pub enum Error {
            Stale,
            Exhausted,
        }

        pub fn reserve(free: u64) -> Result<u64, Error> {
            if free == 0 {
                Err(Error::Exhausted)
            } else {
                Ok(free - 1)
            }
        }
    }

    pub mod capabilities {
        pub enum Error {
            Stale,
            RightsExceeded,
        }

        pub fn derive(rights: u64, requested: u64) -> Result<u64, Error> {
            if requested & !rights != 0 {
                Err(Error::RightsExceeded)
            } else {
                Ok(requested)
            }
        }
    }
}

/// Item R7 of the provable subset: an enumeration that is private in Lean.
/// The case extracts `Phase` without its definition and installs reviewed
/// external declarations that define it as a private enumeration with the
/// `discriminant` attribute of the Aeneas library.
pub mod r7_private_enum {
    pub enum Phase {
        Idle,
        Running,
    }

    pub fn keep(phase: Phase) -> Phase {
        phase
    }
}
