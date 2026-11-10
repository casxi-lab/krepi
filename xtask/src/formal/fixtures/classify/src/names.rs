//! The forms of Rust names that the mapping to inventory keys reads: the
//! methods of a generic type, a default method with two loops, a default
//! method and a free function named `default`, and a derived method that
//! has the key of a hand-written one.

#[derive(PartialEq)]
pub struct Wrapper<T> {
    pub value: T,
}

impl<T> Wrapper<T> {
    pub fn get(&self) -> &T {
        &self.value
    }
}

impl PartialEq<u32> for Wrapper<u32> {
    fn eq(&self, other: &u32) -> bool {
        self.value == *other
    }
}

pub trait Count {
    fn count(&self) -> u32;

    fn twice(&self) -> u32 {
        let mut sum: u32 = 0;
        let mut index = 0;
        while index < 2 {
            sum = sum.wrapping_add(self.count());
            index += 1;
        }
        let mut rounds = 0;
        while rounds < 2 {
            sum = sum.wrapping_add(1);
            rounds += 1;
        }
        sum
    }

    fn default(&self) -> u32 {
        self.count()
    }
}

impl<T> Count for Wrapper<T> {
    fn count(&self) -> u32 {
        1
    }
}

pub fn default(bound: u32) -> u32 {
    let mut count = 0;
    while count < bound {
        count += 1;
    }
    count
}

pub fn equal(a: &Wrapper<u32>, b: &Wrapper<u32>, c: u32) -> bool {
    a == b && *a == c
}
