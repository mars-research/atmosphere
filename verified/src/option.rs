use prusti_contracts::*;

pub enum Option<T> {
    None,
    Some(T),
}

impl<T> Option<T> {
    #[ensures(result.is_none())]
    pub const fn none() -> Self {
        Option::None
    }

    #[ensures(result.is_some())]
    pub const fn some(t: T) -> Self {
        Option::Some(t)
    }

    #[pure]
    pub const fn is_some(&self) -> bool {
        matches!(*self, Option::Some(_))
    }

    #[pure]
    pub const fn is_none(&self) -> bool {
        !self.is_some()
    }
}