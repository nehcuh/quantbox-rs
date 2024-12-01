use thiserror::Error;

#[derive(Debug, Error)]
pub enum QBError {
    #[error("Date Error: {kind} - {details}")]
    DateError {
        kind: DateErrorKind,
        details: String,
    },
}

#[derive(Debug)]
pub enum DateErrorKind {
    Invalid,
    ParseError,
    OutofRange,
}

impl std::fmt::Display for DateErrorKind {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(fmt, "{self:?}")
    }
}

pub type QBResult<T> = std::result::Result<T, QBError>;
