use std::{collections::HashSet, fmt::Display};

use rand::Rng;

use super::Group;

#[derive(Debug, PartialEq)]
pub struct Permutation<const SIZE: usize> {
    map: [usize; SIZE],
}

impl<const SIZE: usize> Permutation<SIZE> {
    /// Returns a permutation in [`cycle notation`] as a String
    ///
    /// The cycles begin with the smallest element first.
    /// The cycles are listed from smallest to largest by first element
    /// 1-cycles are *not* omitted
    ///
    /// Each cycle defines the orbit of an element `x` (successive applications
    /// of the permutation on `x`) without repeating `x`. (x, σ(x), σ(σ(x)), ...)
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// let sigma = Permutation::<6>::identity();
    /// assert_eq!("(1)(2)(3)(4)(5)(6)", sigma.to_cycle_notation());
    /// ```
    ///
    /// [`cycle notation`]: https://en.wikipedia.org/wiki/Permutation#Cycle_notation
    pub fn to_cycle_notation(&self) -> String {
        let mut cycle_notation_string = String::new();
        let mut explored_set = HashSet::new();

        // Depth-first search for cycles
        // Traverses all connected components via outer loop
        for elem in 1..=SIZE {
            if !explored_set.contains(&elem) {
                explored_set.insert(elem);
                cycle_notation_string.push_str(&("(".to_owned() + &elem.to_string()));

                // now explore until we hit a previously explored element
                let mut next_elem = self.map[Self::index_from_elem(elem)];
                while !explored_set.contains(&next_elem) {
                    explored_set.insert(next_elem);
                    cycle_notation_string.push_str(&(" ".to_owned() + &next_elem.to_string()));
                    next_elem = self.map[Self::index_from_elem(next_elem)];
                }
                cycle_notation_string.push(')');
            }
        }
        cycle_notation_string
    }

    /// Returns a permutation in [`cauchy two-line notation`]  as a String
    ///
    /// The first row denotes the elements of the set.
    /// The second row gives the image of the element from the row above
    /// The elements in the first row will be given in ascending order
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// let expected_two_line_notation =
    /// "1 2 3 4 5 6
    /// 1 2 3 4 5 6
    /// ";
    /// let sigma = Permutation::<6>::identity();
    /// assert_eq!(expected_two_line_notation, sigma.to_mapping_notation());
    /// ```
    ///
    /// [`cauchy two-line notation']: https://en.wikipedia.org/wiki/Permutation#Two-line_notation
    pub fn to_mapping_notation(&self) -> String {
        let mut identity_row = String::new();
        let mut mapping_notation = String::new();
        for i in 0..SIZE {
            identity_row.push_str(&((i + 1).to_string() + " "));
            mapping_notation.push_str(&(self.map[i].to_string() + " "));
        }
        // Removes extra spaces from ends of rows
        mapping_notation.pop();
        identity_row.pop();

        identity_row.push('\n');
        identity_row.push_str(&mapping_notation);
        identity_row.push('\n');
        identity_row
    }

    /// Returns a random permutation on SIZE elements
    ///
    /// Generates a random permutation using a [`fisher-yates shuffle`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// println!("{}", Permutation::<6>::random());
    /// ```
    /// [`fisher-yates shuffle`]: https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
    pub fn random() -> Self {
        let mut perm_array = Self::identity_map_array();
        Self::fisher_yates_shuffle(&mut perm_array);
        Self { map: perm_array }
    }

    /// Returns an iterator over all permutations on SIZE elements
    ///
    /// The order is determined by getting the next in [`lexigraphical order`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// for perm in Permutation::<6>::get_elems() {
    ///     println!("{perm}")
    /// }
    /// ```
    /// [`lexigraphical order`]: https://en.wikipedia.org/wiki/Permutation#Generation_in_lexicographic_order
    pub fn get_elems() -> impl Iterator<Item = Self> {
        std::iter::once(Self::identity()).chain(Self::identity())
    }
}

// Group impl
impl<const SIZE: usize> Group for Permutation<SIZE> {
    /// Returns a permutation on SIZE elements that is the result  of the
    /// composition operation between `&self` and `other`
    ///
    /// `&self` is the left operand and `other` is the right operand of composition.
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// let rand_perm = Permutation::<6>::random();
    /// let rand_perm2 = Permutation::<6>::random();
    /// // composition = rand_perm • rand_perm2
    /// let composition = rand_perm.op(&rand_perm2);
    /// println!("{rand_perm} • {rand_perm2} = {composition}");
    /// ```
    fn op(&self, other: &Permutation<SIZE>) -> Self {
        let mut map_copy = self.map;
        (0..SIZE).for_each(|index| {
            map_copy[index] = other.map[Self::index_from_elem(self.map[index])];
        });
        Self { map: map_copy }
    }

    /// Returns the identity element for permutation on SIZE elements
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// let rand_perm = Permutation::<6>::random();
    /// let e = Permutation::<6>::identity();
    /// // composition = rand_perm • e
    /// let composition = rand_perm.op(&e);
    /// assert_eq!(composition, rand_perm);
    /// ```
    fn identity() -> Self {
        Self {
            map: Self::identity_map_array(),
        }
    }

    /// Returns the inverse permutation on SIZE elements of `&self`
    ///
    /// # Examples
    ///
    /// ```
    /// # use groups::permutation::Permutation;
    /// # use groups::Group;
    /// let rand_perm = Permutation::<6>::random();
    /// let rand_perm_inv = rand_perm.inv();
    /// assert_eq!(Permutation::<6>::identity(), rand_perm.op(&rand_perm_inv));
    /// assert_eq!(Permutation::<6>::identity(), rand_perm_inv.op(&rand_perm));
    /// ```
    fn inv(&self) -> Self {
        let mut inv_map = [0; SIZE];
        (0..SIZE).for_each(|index| {
            inv_map[Self::index_from_elem(self.map[index])] = Self::elem_from_index(index);
        });
        Self { map: inv_map }
    }
}

// Private helpers
impl<const SIZE: usize> Permutation<SIZE> {
    fn elem_from_index(index: usize) -> usize {
        index + 1
    }

    fn index_from_elem(elem: usize) -> usize {
        elem - 1
    }

    fn identity_map_array() -> [usize; SIZE] {
        let mut elem_array = [0; SIZE];

        for elem in 1..=SIZE {
            elem_array[Self::index_from_elem(elem)] = elem;
        }
        elem_array
    }

    fn fisher_yates_shuffle(array: &mut [usize]) {
        let mut rng = rand::thread_rng();
        if SIZE > 0 {
            for build_index in 0..(SIZE - 1) {
                let j = rng.gen_range(build_index..SIZE);
                array.swap(build_index, j);
            }
        }
    }
}

impl<const SIZE: usize> Display for Permutation<SIZE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_cycle_notation())
    }
}

impl<const SIZE: usize> Iterator for Permutation<SIZE> {
    type Item = Self;
    fn next(&mut self) -> Option<Self::Item> {
        let i = (0..SIZE - 1)
            .rev()
            .find(|&i| self.map[i] < self.map[i + 1])?;
        let j = (i + 1..SIZE).rev().find(|&j| self.map[j] > self.map[i])?;
        self.map.swap(i, j);
        self.map[i + 1..].reverse();
        Some(Permutation { map: self.map })
    }
}

#[cfg(test)]
mod permutation_tests {
    use super::Group;
    use super::Permutation;

    #[test]
    fn s5_identity_is_identity() {
        for perm in Permutation::<5>::get_elems() {
            assert_eq!(perm, perm.op(&Permutation::<5>::identity()));
            assert_eq!(perm, Permutation::<5>::identity().op(&perm));
        }
    }

    #[test]
    fn s5_test_associativity() {
        for p1 in Permutation::<5>::get_elems() {
            for p2 in Permutation::<5>::get_elems() {
                for p3 in Permutation::<5>::get_elems() {
                    let p1_p2 = p1.op(&p2);
                    let p2_p3 = p2.op(&p3);
                    assert_eq!(p1_p2.op(&p3), p1.op(&p2_p3));
                }
            }
        }
    }

    #[test]
    fn s5_test_inverse_existence() {
        for perm in Permutation::<5>::get_elems() {
            let inv = perm.inv();
            assert_eq!(perm.op(&inv), Permutation::<5>::identity());
        }
    }

    #[test]
    fn s5_test_closure() {
        let s5_set: Vec<Permutation<5>> = Permutation::<5>::get_elems().collect();
        for p1 in Permutation::<5>::get_elems() {
            for p2 in Permutation::<5>::get_elems() {
                assert!(s5_set.iter().any(|elem| *elem == p1.op(&p2)));
            }
        }
    }

    #[test]
    fn s5_is_not_abelian() {
        let elem_count = Permutation::<5>::get_elems().count();
        let mut s5_mul_set: Vec<Permutation<5>> = Vec::with_capacity(elem_count * elem_count);
        for p1 in Permutation::<5>::get_elems() {
            for p2 in Permutation::<5>::get_elems() {
                s5_mul_set.push(p1.op(&p2));
            }
        }
        let mut some_non_commutative = false;
        'outer: for i in 0..elem_count {
            for j in 0..elem_count {
                if !some_non_commutative {
                    some_non_commutative =
                        s5_mul_set[i * elem_count + j] != s5_mul_set[j * elem_count + i];
                } else {
                    dbg!(some_non_commutative);
                    break 'outer;
                }
            }
        }
        assert!(some_non_commutative);
    }
}
