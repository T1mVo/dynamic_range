use std::marker::PhantomData;

use super::*;

use ::clap::{
    builder::TypedValueParser,
    error::{Error as ClapError, ErrorKind},
    Arg, Command,
};

#[derive(Clone)]
pub struct DynamicRangeValueParser<T>(PhantomData<T>);

impl<T> DynamicRangeValueParser<T> {
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> Default for DynamicRangeValueParser<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: FromStr + Clone + Send + Sync + 'static> TypedValueParser for DynamicRangeValueParser<T> {
    type Value = DynamicRange<T>;

    fn parse_ref(
        &self,
        _: &Command,
        _: Option<&Arg>,
        value: &std::ffi::OsStr,
    ) -> Result<DynamicRange<T>, ClapError> {
        let range = DynamicRange::<T>::from_str(value.to_string_lossy().as_ref())
            .map_err(|err| ClapError::raw(ErrorKind::ValueValidation, err.to_string()))?;

        Ok(range)
    }
}
