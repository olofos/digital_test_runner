use thiserror::Error;

#[derive(Debug, Error)]
pub enum RunError<T> {
    #[error("Driver error")]
    Driver(#[from] T),
    #[error("Runtime error")]
    Runtime(anyhow::Error),
}
