use curve25519_dalek::{RistrettoPoint, Scalar};
use merlin::Transcript;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};

pub type DlogWitness = Scalar;

/// Statement for the discrete logarithm proof: x * G = X
pub struct DlogStatement {
    pub G: RistrettoPoint,
    pub X: RistrettoPoint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DlogProof {
    pub c: Scalar,
    pub s: Scalar,
}

pub fn prove_dlog(
    trans: &mut Transcript,
    wit: &DlogWitness,
    stmt: &DlogStatement,
) -> DlogProof {
    // Ensure the witness is valid
    assert!(wit * stmt.G == stmt.X);

    let mut rng = OsRng;
    let r = Scalar::random(&mut rng);
    let R = r * stmt.G;

    trans.append_message(b"G", stmt.G.compress().as_bytes());
    trans.append_message(b"X", stmt.X.compress().as_bytes());
    trans.append_message(b"R", R.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);
    let s = r + c * wit;

    DlogProof { c, s }
}

pub fn verify_dlog(
    trans: &mut Transcript,
    proof: &DlogProof,
    stmt: &DlogStatement,
) -> bool {
    // recompute the R: R = s * G - c * X
    let R = proof.s * stmt.G - proof.c * stmt.X;

    trans.append_message(b"G", stmt.G.compress().as_bytes());
    trans.append_message(b"X", stmt.X.compress().as_bytes());
    trans.append_message(b"R", R.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);

    c == proof.c
}
