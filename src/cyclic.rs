use std::fmt::Display;

use rand::Rng;

use super::Group;

#[derive(Debug, PartialEq)]
pub struct Cyclic<const SIZE: usize> {
    elem: usize,
}

impl<const SIZE: usize> Cyclic<SIZE> {
    /// Returns a random element of the cyclic group of order SIZE
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::cyclic::Cyclic;
    /// # use groups::Group;
    /// println!("{}", Cyclic::<6>::random());
    /// ```
    pub fn random() -> Self {
        let mut rng = rand::thread_rng();
        Self {
            elem: rng.gen_range(0..SIZE),
        }
    }

    /// Returns an iterator over all elements of cyclic group of order SIZE
    ///
    /// The next element is the result of the binary operation on the current element
    /// and a generator element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::cyclic::Cyclic;
    /// # use groups::Group;
    /// for c in Cyclic::<6>::get_elems().skip(1) {
    ///     assert!(c != Cyclic::<6>::identity());
    /// }
    /// ```
    pub fn get_elems() -> impl Iterator<Item = Self> {
        std::iter::once(Self::identity()).chain(Self::identity())
    }
}

impl<const SIZE: usize> Iterator for Cyclic<SIZE> {
    type Item = Self;

    // could rewrite this using an element defined as the generator - `1` for example
    // and then just do Some(self.op(Self::generator()))
    // could consider allowing this to be an infinite iterator too - forcing users to .take()
    fn next(&mut self) -> Option<Self::Item> {
        if self.elem + 1 == SIZE {
            None
        } else {
            self.elem = (self.elem + 1) % SIZE;
            Some(Self { elem: self.elem })
        }
    }
}

impl<const SIZE: usize> Group for Cyclic<SIZE> {
    /// Returns an element of the cyclic group of order SIZE that is the result of the
    /// binary operation between `&self` and `other`
    ///
    /// `&self` is the left operand and `other` is the right operand of composition.
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::cyclic::Cyclic;
    /// # use groups::Group;
    /// let c1 = Cyclic::<6>::random();
    /// let c2 = Cyclic::<6>::random();
    /// // result = c1 • c2
    /// let result = c1.op(&c2);
    /// println!("{c1} • {c2} = {result}");
    /// ```
    fn op(&self, other: &Cyclic<SIZE>) -> Self {
        Self {
            elem: (self.elem + other.elem) % SIZE,
        }
    }

    /// Returns the inverse of `&self` in the cyclic group of order SIZE
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::cyclic::Cyclic;
    /// # use groups::Group;
    /// let c = Cyclic::<6>::random();
    /// let c_inv = c.inv();
    /// // e = c • c^(-1)
    /// assert_eq!(Cyclic::<6>::identity(), c.op(&c_inv));
    /// // e = c^(-1) • c
    /// assert_eq!(Cyclic::<6>::identity(), c_inv.op(&c));
    /// ```
    fn inv(&self) -> Self {
        Self {
            elem: (SIZE - self.elem) % SIZE,
        }
    }

    /// Returns the identity element for cyclic group of order SIZE
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::cyclic::Cyclic;
    /// # use groups::Group;
    /// let c1 = Cyclic::<6>::random();
    /// let e =Cyclic::<6>::identity();
    /// // result = c1 • e
    /// let result = c1.op(&e);
    /// // result should be c1 since: c1 • e = c1
    /// assert_eq!(result, c1);
    /// ```
    fn identity() -> Self {
        Self { elem: 0 }
    }
}

impl<const SIZE: usize> Display for Cyclic<SIZE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.elem)
    }
}

#[cfg(test)]
mod cyclic_tests {
    use super::Group;

    use super::Cyclic;

    #[test]
    fn c5_identity_is_identity() {
        let e = Cyclic::<5>::identity();
        for c in Cyclic::<5>::get_elems() {
            assert_eq!(e.op(&c), c);
            assert_eq!(c.op(&e), c);
        }
    }

    #[test]
    fn c5_2_order_is_5() {
        let c5_2 = Cyclic::<5>::identity()
            .nth(2)
            .expect("There is not a third value in Cyclic group from identity");
        let mut res = Cyclic::<5>::identity();
        for chain_limit in 0..4 {
            res = Cyclic::<5>::identity().op(&c5_2);
            for _ in 1..=chain_limit {
                res = res.op(&c5_2);
            }
            assert!(res != Cyclic::<5>::identity());
        }
        // One more op and order of element is found -- 2^5 (mod 5) = 0 (mod 5)
        assert_eq!(res.op(&c5_2), Cyclic::<5>::identity());
    }

    #[test]
    fn c5_test_associativity() {
        for x in Cyclic::<5>::get_elems() {
            for y in Cyclic::<5>::get_elems() {
                for z in Cyclic::<5>::get_elems() {
                    let y_z = y.op(&z);
                    let x_y = x.op(&y);
                    assert_eq!(x.op(&y_z), x_y.op(&z));
                }
            }
        }
    }

    #[test]
    fn c5_test_inverse_existence() {
        for x in Cyclic::<5>::get_elems() {
            let x_inv = x.inv();
            assert_eq!(x.op(&x_inv), Cyclic::<5>::identity());
        }
    }

    #[test]
    fn c5_test_closure() {
        let c5_set: Vec<Cyclic<5>> = Cyclic::<5>::get_elems().collect();
        for x in Cyclic::<5>::get_elems() {
            for y in Cyclic::<5>::get_elems() {
                assert!(c5_set.iter().any(|elem| *elem == x.op(&y)));
            }
        }
    }

    #[test]
    fn c5_is_abelian() {
        for x in Cyclic::<5>::get_elems() {
            for y in Cyclic::<5>::get_elems() {
                assert_eq!(x.op(&y), y.op(&x));
            }
        }
    }
}
