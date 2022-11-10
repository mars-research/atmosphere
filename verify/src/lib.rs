#![no_std]

use prusti_contracts::*;
use core::option::Option;

#[extern_spec]
impl<T> Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

#[pure]
#[requires(0 <= n)]
#[requires(n < 1_000_000)]
#[ensures(result == n * (n + 1) / 2)]
pub fn model(n: i64) -> i64 {
    n * (n + 1) / 2
}

#[requires(0 <= n)]
#[requires(n < 1_000_000)]
#[ensures(result == model(n))]
pub fn gauss(n: i64) -> i64 {
    let mut res: i64 = 0;
    let mut i: i64 = 0;
    while i < n {
        body_invariant!(0 <= i && i < n);
        body_invariant!(res == model(i));

        i = i + 1;
        res = res + i;
    }
    res
}

#[requires(n < 32)]
#[ensures(result == 4 * n)]
pub fn cursed_quadruple_1(n: u8) -> u8 {
    n + n + n + n
}

#[requires(n > 0)]
#[requires(n < 32)]
#[ensures(result == 4 * n)]
pub fn cursed_quadruple_2(n: u8) -> u8 {
    let mut result = n;
    result += n + n;

    if result > n {
        result += n;
    }

    if result < 4 * n {
        result = 0;
    }

    result
}