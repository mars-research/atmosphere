extern crate core;

use prusti_contracts::*;

#[extern_spec]
impl<T> core::option::Option<T> {

    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    #[ensures(self.is_none() == !result)]
    pub const fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub const fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn expect(self, msg: &str) -> T;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

#[extern_spec]
impl<T: core::cmp::PartialEq> core::option::Option<T> {
    #[ensures(self.is_none() ==> (result == default))]
    pub fn unwrap_or(self, default: T) -> T;
}