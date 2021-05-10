//! Kernel command line utilities.

/// A command line component.
#[derive(Debug)]
pub enum Component<'a> {
    /// A flag.
    ///
    /// Example: nocolor
    Flag(&'a str),

    /// A key-value pair.
    ///
    /// Example: script=vmx_test
    KeyValue((&'a str, &'a str)),
}

impl<'a> Component<'a> {
    fn from_str(s: &'a str) -> Self {
        match s.find('=') {
            Some(index) => Self::KeyValue((&s[0..index], &s[index + 1..])),
            None => Self::Flag(s),
        }
    }
}

pub struct Iterator<'a> {
    split: core::str::Split<'a, char>,
}

impl<'a> core::iter::Iterator for Iterator<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_component = self.split.next();

        loop {
            match next_component {
                None => {
                    return None;
                }
                Some(s) => {
                    if s.is_empty() {
                        next_component = self.split.next();
                        continue;
                    }

                    return Some(Component::from_str(s));
                }
            }
        }
    }
}

/// Returns an iterator over command line components.
pub fn get_iter() -> Iterator<'static> {
    Iterator {
        split: super::get_command_line().split(' '),
    }
}

/// Returns the first value of a given key.
///
/// This does not allocate any new data structures and
/// is O(N).
pub fn get_first_value(key: &str) -> Option<&'static str> {
    for component in get_iter() {
        if let Component::KeyValue((k, v)) = component {
            if key == k {
                return Some(v);
            }
        }
    }

    None
}
