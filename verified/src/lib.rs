#![no_std]

pub mod option;

pub mod prelude {
    pub use super::option::Option;
}

pub mod test {

    use prusti_contracts::*;

    #[test]
    fn test() {
        let _ = model(1);
        let _ = gauss(1);
        let _ = cursed_quadruple_1(1);
        let _ = cursed_quadruple_2(1);
        let _ = cursed_test(crate::option::Option::Some(1));
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

    #[ensures(n.is_some() ==> (result == true))]
    pub fn cursed_test<T>(n: crate::option::Option<T>) -> bool {
        if n.is_some() {
            assert!(!n.is_none());
            return true;
        }
        false
    }

}