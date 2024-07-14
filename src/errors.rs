use thiserror::Error;

#[derive(Debug, Error)]
/// Error returned from DataRowIterator
pub enum RunError<T> {
    /// Driver error
    #[error("Driver error")]
    Driver(#[from] T),
    /// Runtime error
    #[error("Runtime error")]
    Runtime(anyhow::Error),
}
