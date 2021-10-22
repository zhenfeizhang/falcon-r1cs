use ark_relations::r1cs::SynthesisError;
use displaydoc::Display;

/// A `enum` specifying the possible failure modes of Falcon-r1cs.
#[derive(Display, Debug)]
pub enum FalconR1CSError {
    /// An error during (de)serialization {0}
    SerializationError(ark_serialize::SerializationError),
    /// Arkworks' SynthesisError {0}
    SynthesisError(SynthesisError),
    /// Invalid parameter {0}
    InvalidParameters(String),
}

impl From<SynthesisError> for FalconR1CSError {
    fn from(e: SynthesisError) -> Self {
        Self::SynthesisError(e)
    }
}
