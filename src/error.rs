use thiserror::Error;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("Could not parse value '{value}' to type of '{type_name}'")]
    ParseError { value: String, type_name: String },
    #[error("Invalid type of range: '{range}'")]
    InvalidRangeError { range: String },
}
