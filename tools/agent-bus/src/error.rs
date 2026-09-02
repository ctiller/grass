use thiserror::Error;

#[derive(Debug, Error)]
pub enum AbError {
    #[error("{0}")]
    Invalid(String),
    #[error("io error at {path}: {source}")]
    Io {
        path: String,
        #[source]
        source: std::io::Error,
    },
    #[error("git error: {0}")]
    Git(String),
    #[error("json error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("{0}")]
    Other(#[from] anyhow::Error),
}

pub type AbResult<T> = Result<T, AbError>;

pub fn invalid<S: Into<String>>(s: S) -> AbError {
    AbError::Invalid(s.into())
}
