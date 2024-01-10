#![forbid(unsafe_code)]

use std::{
    any::type_name,
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum DynamicRange<T> {
    Range(Range<T>),
    RangeFrom(RangeFrom<T>),
    RangeFull,
    RangeInclusive(RangeInclusive<T>),
    RangeTo(RangeTo<T>),
    RangeToInclusive(RangeToInclusive<T>),
}

impl<T: FromStr> FromStr for DynamicRange<T> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let caps = REGEX.captures(s).ok_or(Error::InvalidRangeError {
            range: s.to_string(),
        })?;

        let (_, [start, inclusive, end]) = caps.extract();

        match (!inclusive.is_empty(), !start.is_empty(), !end.is_empty()) {
            (true, true, true) => {
                let start = try_parse_value(start)?;
                let end = try_parse_value(end)?;
                Ok(Self::RangeInclusive(RangeInclusive::<T>::new(start, end)))
            }
            (true, false, true) => {
                let end = try_parse_value(end)?;
                Ok(Self::RangeToInclusive(RangeToInclusive::<T> { end }))
            }
            (true, true, false) => {
                let start = try_parse_value(start)?;
                Ok(Self::RangeFrom(RangeFrom::<T> { start }))
            }
            (true, false, false) => Err(Error::InvalidRangeError {
                range: s.to_string(),
            }),
            (false, true, true) => {
                let start = try_parse_value(start)?;
                let end = try_parse_value(end)?;
                Ok(Self::Range(Range::<T> { start, end }))
            }
            (false, false, true) => {
                let end = try_parse_value(end)?;
                Ok(Self::RangeTo(RangeTo::<T> { end }))
            }
            (false, true, false) => {
                let start = try_parse_value(start)?;
                Ok(Self::RangeFrom(RangeFrom::<T> { start }))
            }
            (false, false, false) => Ok(Self::RangeFull),
        }
    }
}

fn try_parse_value<T: FromStr>(value: &str) -> error::Result<T> {
    T::from_str(value).map_err(|_| Error::ParseError {
        value: value.to_string(),
        type_name: type_name::<T>().to_string(),
    })
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

impl<T> From<Range<T>> for DynamicRange<T> {
    fn from(value: Range<T>) -> Self {
        Self::Range(value)
    }
}

impl<T> From<RangeFrom<T>> for DynamicRange<T> {
    fn from(value: RangeFrom<T>) -> Self {
        Self::RangeFrom(value)
    }
}

impl<T> From<RangeFull> for DynamicRange<T> {
    fn from(_: RangeFull) -> Self {
        Self::RangeFull
    }
}

impl<T> From<RangeTo<T>> for DynamicRange<T> {
    fn from(value: RangeTo<T>) -> Self {
        Self::RangeTo(value)
    }
}

impl<T> From<RangeInclusive<T>> for DynamicRange<T> {
    fn from(value: RangeInclusive<T>) -> Self {
        Self::RangeInclusive(value)
    }
}

impl<T> From<RangeToInclusive<T>> for DynamicRange<T> {
    fn from(value: RangeToInclusive<T>) -> Self {
        Self::RangeToInclusive(value)
    }
}

impl<T> RangeBounds<T> for DynamicRange<T> {
    fn start_bound(&self) -> Bound<&T> {
        match self {
            DynamicRange::Range(r) => r.start_bound(),
            DynamicRange::RangeFrom(r) => r.start_bound(),
            DynamicRange::RangeFull => Bound::Unbounded,
            DynamicRange::RangeInclusive(r) => r.start_bound(),
            DynamicRange::RangeTo(r) => r.start_bound(),
            DynamicRange::RangeToInclusive(r) => r.start_bound(),
        }
    }

    fn end_bound(&self) -> Bound<&T> {
        match self {
            DynamicRange::Range(r) => r.end_bound(),
            DynamicRange::RangeFrom(r) => r.end_bound(),
            DynamicRange::RangeFull => Bound::Unbounded,
            DynamicRange::RangeInclusive(r) => r.end_bound(),
            DynamicRange::RangeTo(r) => r.end_bound(),
            DynamicRange::RangeToInclusive(r) => r.end_bound(),
        }
    }
}

impl<T> RangeBounds<T> for DynamicRange<&T> {
    fn start_bound(&self) -> Bound<&T> {
        match self {
            DynamicRange::Range(r) => r.start_bound(),
            DynamicRange::RangeFrom(r) => r.start_bound(),
            DynamicRange::RangeFull => Bound::Unbounded,
            DynamicRange::RangeInclusive(r) => r.start_bound(),
            DynamicRange::RangeTo(r) => r.start_bound(),
            DynamicRange::RangeToInclusive(r) => r.start_bound(),
        }
    }

    fn end_bound(&self) -> Bound<&T> {
        match self {
            DynamicRange::Range(r) => r.end_bound(),
            DynamicRange::RangeFrom(r) => r.end_bound(),
            DynamicRange::RangeFull => Bound::Unbounded,
            DynamicRange::RangeInclusive(r) => r.end_bound(),
            DynamicRange::RangeTo(r) => r.end_bound(),
            DynamicRange::RangeToInclusive(r) => r.end_bound(),
        }
    }
}

impl<T: PartialOrd<T>> DynamicRange<T> {
    pub fn contains<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>,
    {
        <Self as RangeBounds<T>>::contains(self, item)
    }
}

impl<T> Index<DynamicRange<usize>> for [T] {
    type Output = [T];

    fn index(&self, index: DynamicRange<usize>) -> &Self::Output {
        match index {
            DynamicRange::Range(r) => &self[r],
            DynamicRange::RangeFrom(r) => &self[r],
            DynamicRange::RangeFull => self,
            DynamicRange::RangeTo(r) => &self[r],
            DynamicRange::RangeInclusive(r) => &self[r],
            DynamicRange::RangeToInclusive(r) => &self[r],
        }
    }
}

impl<T> IndexMut<DynamicRange<usize>> for [T] {
    fn index_mut(&mut self, index: DynamicRange<usize>) -> &mut Self::Output {
        match index {
            DynamicRange::Range(r) => &mut self[r],
            DynamicRange::RangeFrom(r) => &mut self[r],
            DynamicRange::RangeFull => self,
            DynamicRange::RangeTo(r) => &mut self[r],
            DynamicRange::RangeInclusive(r) => &mut self[r],
            DynamicRange::RangeToInclusive(r) => &mut self[r],
        }
    }
}

impl<T> IntoIterator for DynamicRange<T>
where
    T: PrimInt,
{
    type Item = T;

    type IntoIter = DynamicRangeIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            DynamicRange::Range(r) => DynamicRangeIterator {
                start: r.start,
                end: r.end,
                inclusive: false,
            },
            DynamicRange::RangeFrom(r) => DynamicRangeIterator {
                start: r.start,
                end: T::max_value(),
                inclusive: false,
            },
            DynamicRange::RangeFull => DynamicRangeIterator {
                start: T::min_value(),
                end: T::max_value(),
                inclusive: true,
            },
            DynamicRange::RangeInclusive(r) => DynamicRangeIterator {
                start: *r.start(),
                end: *r.end(),
                inclusive: true,
            },
            DynamicRange::RangeTo(r) => DynamicRangeIterator {
                start: T::min_value(),
                end: r.end,
                inclusive: false,
            },
            DynamicRange::RangeToInclusive(r) => DynamicRangeIterator {
                start: T::min_value(),
                end: r.end,
                inclusive: true,
            },
        }
    }
}

pub struct DynamicRangeIterator<T> {
    start: T,
    end: T,
    inclusive: bool,
}

impl<T> Iterator for DynamicRangeIterator<T>
where
    T: PrimInt,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.inclusive {
            if self.start <= self.end {
                let index = self.start;
                self.start = self.start + T::one();
                Some(index)
            } else {
                None
            }
        } else if self.start < self.end {
            let index = self.start;
            self.start = self.start + T::one();
            Some(index)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::HashMap,
        fmt::{Debug, Display},
    };

    use num_traits::{Bounded, PrimInt};

    use super::*;

    use error::Result;

    fn num_values<T: Bounded + Display>() -> HashMap<String, Result<DynamicRange<T>>> {
        HashMap::from([
            // Range
            (
                format!("{}..{}", T::min_value(), T::max_value()),
                Ok(DynamicRange::Range(T::min_value()..T::max_value())),
            ),
            // RangeFrom
            (
                format!("{}..", T::min_value()),
                Ok(DynamicRange::RangeFrom(T::min_value()..)),
            ),
            // RangeFull
            (String::from(".."), Ok(DynamicRange::RangeFull)),
            // RangeInclusive
            (
                format!("{}..={}", T::min_value(), T::max_value()),
                Ok(DynamicRange::RangeInclusive(
                    T::min_value()..=T::max_value(),
                )),
            ),
            // RangeTo
            (
                format!("..{}", T::max_value()),
                Ok(DynamicRange::RangeTo(..T::max_value())),
            ),
            // RangeToInclusive
            (
                format!("..={}", T::max_value()),
                Ok(DynamicRange::RangeToInclusive(..=T::max_value())),
            ),
            // End overflow ParsingError
            (
                format!("{}..{}1", T::min_value(), T::max_value()),
                Err(Error::ParseError {
                    value: format!("{}1", T::max_value()),
                    type_name: type_name::<T>().to_string(),
                }),
            ),
            // Start overflow ParsingError
            (
                format!("{}1..{}", T::max_value(), T::min_value()),
                Err(Error::ParseError {
                    value: format!("{}1", T::max_value()),
                    type_name: type_name::<T>().to_string(),
                }),
            ),
            // Invalid InclusiveRange
            (
                String::from("..="),
                Err(Error::InvalidRangeError {
                    range: String::from("..="),
                }),
            ),
        ])
    }

    fn test<T: PrimInt + Display + FromStr + Debug>() {
        let values = num_values::<T>();

        for (str, expected) in values {
            let actual = DynamicRange::<T>::from_str(&str);

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn i128() {
        test::<i128>();
    }

    #[test]
    fn i64() {
        test::<i64>();
    }

    #[test]
    fn i32() {
        test::<i32>();
    }

    #[test]
    fn i16() {
        test::<i16>();
    }

    #[test]
    fn i8() {
        test::<i8>();
    }

    #[test]
    fn u128() {
        test::<u128>();
    }

    #[test]
    fn u64() {
        test::<u64>();
    }

    #[test]
    fn u32() {
        test::<u32>();
    }

    #[test]
    fn u16() {
        test::<u16>();
    }

    #[test]
    fn u8() {
        test::<u8>();
    }
}
