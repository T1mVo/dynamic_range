#![forbid(unsafe_code)]

use std::{
    any::type_name,
    iter::FusedIterator,
    ops::{
        Bound, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
        RangeToInclusive,
    },
    str::FromStr,
};

use num_traits::PrimInt;
use once_cell::sync::Lazy;
use regex_lite::Regex;

use error::Error;

#[cfg(feature = "clap")]
pub mod clap;

pub mod error;

const REGEX_STR: &str = r"^(-?[\w\.]*)\.\.(=?)(-?[\w\.]*)$";

static REGEX: Lazy<Regex> = Lazy::new(|| Regex::new(REGEX_STR).expect("Could not compile regex"));

/// Represents a range with start and end bounds that can be dynamic.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DynamicRange<T> {
    start: Bound<T>,
    end: Bound<T>,
}

impl<T: Copy> Copy for DynamicRange<T> {}

impl<T> DynamicRange<T> {
    /// Creates a new `DynamicRange` with the provided start and end bounds.
    ///
    /// # Parameters
    ///
    /// - `start`: The start bound of the range.
    /// - `end`: The end bound of the range.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` with the specified bounds.
    pub const fn new(start: Bound<T>, end: Bound<T>) -> Self {
        Self { start, end }
    }

    /// Creates a new `DynamicRange` with inclusive start and exclusive end bounds.
    ///
    /// # Parameters
    ///
    /// - `start`: The inclusive start value.
    /// - `end`: The exclusive end value.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` with the specified bounds.
    pub const fn range(start: T, end: T) -> Self {
        Self {
            start: Bound::Included(start),
            end: Bound::Excluded(end),
        }
    }

    /// Creates a new `DynamicRange` with inclusive start and inclusive end bounds.
    ///
    /// # Parameters
    ///
    /// - `start`: The inclusive start value.
    /// - `end`: The inclusive end value.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` with the specified bounds.
    pub const fn range_inclusive(start: T, end: T) -> Self {
        Self {
            start: Bound::Included(start),
            end: Bound::Included(end),
        }
    }

    /// Creates a new `DynamicRange` that includes all values up to, but not including, the specified end.
    ///
    /// # Parameters
    ///
    /// - `end`: The exclusive end value.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` that ends before the specified value.
    pub const fn range_to(end: T) -> Self {
        Self {
            start: Bound::Unbounded,
            end: Bound::Excluded(end),
        }
    }

    /// Creates a new `DynamicRange` that includes all values up to and including the specified end.
    ///
    /// # Parameters
    ///
    /// - `end`: The inclusive end value.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` that ends at the specified value.
    pub const fn range_to_inclusive(end: T) -> Self {
        Self {
            start: Bound::Unbounded,
            end: Bound::Included(end),
        }
    }

    /// Creates a new `DynamicRange` that starts from the specified value and includes all subsequent values.
    ///
    /// # Parameters
    ///
    /// - `start`: The inclusive start value.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` that starts from the specified value.
    pub const fn range_from(start: T) -> Self {
        Self {
            start: Bound::Included(start),
            end: Bound::Unbounded,
        }
    }

    /// Creates a new `DynamicRange` that includes all possible values.
    ///
    /// # Returns
    ///
    /// A new `DynamicRange` that is unbounded at both the start and end.
    pub const fn range_full() -> Self {
        Self {
            start: Bound::Unbounded,
            end: Bound::Unbounded,
        }
    }
}

impl<T> From<Range<T>> for DynamicRange<T> {
    fn from(value: Range<T>) -> Self {
        Self::range(value.start, value.end)
    }
}

impl<T> From<RangeFrom<T>> for DynamicRange<T> {
    fn from(value: RangeFrom<T>) -> Self {
        Self::range_from(value.start)
    }
}

impl<T> From<RangeFull> for DynamicRange<T> {
    fn from(_: RangeFull) -> Self {
        Self::range_full()
    }
}

impl<T> From<RangeTo<T>> for DynamicRange<T> {
    fn from(value: RangeTo<T>) -> Self {
        Self::range_to(value.end)
    }
}

impl<T: Clone> From<RangeInclusive<T>> for DynamicRange<T> {
    fn from(value: RangeInclusive<T>) -> Self {
        let start = value.start().clone();
        let end = value.end().clone();

        Self::range_inclusive(start, end)
    }
}

impl<T> From<RangeToInclusive<T>> for DynamicRange<T> {
    fn from(value: RangeToInclusive<T>) -> Self {
        Self::range_to_inclusive(value.end)
    }
}

fn try_parse_value<T: FromStr>(value: &str) -> error::Result<T> {
    T::from_str(value).map_err(|_| Error::ParseError {
        value: value.to_string(),
        type_name: type_name::<T>().to_string(),
    })
}

impl<T: FromStr> FromStr for DynamicRange<T> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let caps = REGEX.captures(s).ok_or(Error::InvalidRangeError {
            range: s.to_string(),
        })?;

        let (_, [start, inclusive, end]) = caps.extract();

        if inclusive.is_empty() {
            match (!start.is_empty(), !end.is_empty()) {
                (true, true) => {
                    let start = try_parse_value(start)?;
                    let end = try_parse_value(end)?;
                    Ok(Self::range(start, end))
                }
                (false, true) => {
                    let end = try_parse_value(end)?;
                    Ok(Self::range_to(end))
                }
                (true, false) => {
                    let start = try_parse_value(start)?;
                    Ok(Self::range_from(start))
                }
                (false, false) => Ok(Self::range_full()),
            }
        } else {
            match (!start.is_empty(), !end.is_empty()) {
                (true, true) => {
                    let start = try_parse_value(start)?;
                    let end = try_parse_value(end)?;
                    Ok(Self::range_inclusive(start, end))
                }
                (false, true) => {
                    let end = try_parse_value(end)?;
                    Ok(Self::range_to_inclusive(end))
                }
                _ => Err(Error::InvalidRangeError {
                    range: s.to_string(),
                }),
            }
        }
    }
}

impl<T: FromStr> TryFrom<String> for DynamicRange<T> {
    type Error = Error;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::from_str(&value)
    }
}

impl<T: FromStr> TryFrom<&String> for DynamicRange<T> {
    type Error = Error;

    fn try_from(value: &String) -> Result<Self, Self::Error> {
        Self::from_str(value)
    }
}

impl<T: FromStr> TryFrom<&str> for DynamicRange<T> {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::from_str(value)
    }
}

impl<T> RangeBounds<T> for DynamicRange<T> {
    fn start_bound(&self) -> Bound<&T> {
        self.start.as_ref()
    }

    fn end_bound(&self) -> Bound<&T> {
        self.end.as_ref()
    }
}

impl<T> RangeBounds<T> for DynamicRange<&T> {
    fn start_bound(&self) -> Bound<&T> {
        self.start
    }

    fn end_bound(&self) -> Bound<&T> {
        self.end
    }
}

impl<T> Index<DynamicRange<usize>> for [T] {
    type Output = [T];

    fn index(&self, index: DynamicRange<usize>) -> &Self::Output {
        &self[(index.start, index.end)]
    }
}

impl<T> IndexMut<DynamicRange<usize>> for [T] {
    fn index_mut(&mut self, index: DynamicRange<usize>) -> &mut Self::Output {
        &mut self[(index.start, index.end)]
    }
}

impl Index<DynamicRange<usize>> for str {
    type Output = str;

    fn index(&self, index: DynamicRange<usize>) -> &Self::Output {
        &self[(index.start, index.end)]
    }
}

impl IndexMut<DynamicRange<usize>> for str {
    fn index_mut(&mut self, index: DynamicRange<usize>) -> &mut Self::Output {
        &mut self[(index.start, index.end)]
    }
}

impl<T: PrimInt> IntoIterator for DynamicRange<T> {
    type Item = T;
    type IntoIter = DynamicRangeIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        DynamicRangeIterator::new(self.start, self.end)
    }
}

pub struct DynamicRangeIterator<T> {
    index: Option<T>,
    start: Bound<T>,
    end: Bound<T>,
    exhausted: Exhausted,
}

impl<T: PrimInt> DynamicRangeIterator<T> {
    fn start(&self) -> Option<T> {
        match self.start {
            Bound::Included(start) => Some(start),
            Bound::Excluded(start) => start.checked_add(&T::one()),
            Bound::Unbounded => Some(T::min_value()),
        }
    }

    fn end(&self) -> Option<T> {
        match self.end {
            Bound::Included(end) => Some(end),
            Bound::Excluded(end) => end.checked_sub(&T::one()),
            Bound::Unbounded => Some(T::max_value()),
        }
    }
}

#[derive(PartialEq, Eq)]
enum Exhausted {
    None,
    Upper,
    Lower,
}

impl<T> DynamicRangeIterator<T>
where
    T: PrimInt,
{
    pub fn new(start: Bound<T>, end: Bound<T>) -> Self {
        Self {
            index: None,
            start,
            end,
            exhausted: Exhausted::None,
        }
    }
}

impl<T: PrimInt> Iterator for DynamicRangeIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted == Exhausted::Upper {
            return None;
        }

        let mut index = self.index.or_else(|| self.start())?;
        let start = self.start()?;
        let end = self.end()?;

        if index < start {
            index = start;
        }

        if index <= end {
            match index.checked_add(&T::one()) {
                Some(index) => self.index = Some(index),
                None => self.exhausted = Exhausted::Upper,
            };

            Some(index)
        } else {
            None
        }
    }
}

impl<T: PrimInt> DoubleEndedIterator for DynamicRangeIterator<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted == Exhausted::Lower {
            return None;
        }

        let mut index = self.index.or_else(|| self.end())?;
        let start = self.start()?;
        let end = self.end()?;

        if index > end {
            index = end;
        }

        if index >= start {
            match index.checked_sub(&T::one()) {
                Some(index) => self.index = Some(index),
                None => self.exhausted = Exhausted::Lower,
            };

            Some(index)
        } else {
            None
        }
    }
}

impl<T: PrimInt> ExactSizeIterator for DynamicRangeIterator<T> {
    fn len(&self) -> usize {
        let start = match self.start() {
            // Cast should be impossible to fail
            Some(start) => start.to_usize().expect("Could not cast to usize"),
            None => return 0,
        };

        let end = match self.end() {
            // Cast should be impossible to fail
            Some(end) => end.to_usize().expect("Could not cast to usize"),
            None => return 0,
        };

        // Add one to account for last number not being included
        end - start + 1
    }
}

impl<T: PrimInt> FusedIterator for DynamicRangeIterator<T> {}

#[cfg(test)]
mod tests {}
