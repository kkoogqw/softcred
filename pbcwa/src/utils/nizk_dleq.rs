use bulletproofs::r1cs::R1CSError;
use curve25519_dalek::{RistrettoPoint, Scalar};
use merlin::Transcript;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};

pub type DleqWitness = Scalar;

/// The statement for the discrete logarithm equality proof:
/// (x * G = X) & (x * A = B)
pub struct DleqStatement {
    pub G: RistrettoPoint,
    pub X: RistrettoPoint,
    pub A: RistrettoPoint,
    pub B: RistrettoPoint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DleqProof {
    pub c: Scalar,
    pub s: Scalar,
}

pub fn prove_dleq(
    trans: &mut Transcript,
    wit: &DleqWitness,
    stmt: &DleqStatement,
) -> DleqProof {
    // Ensure the witness is valid
    assert!(wit * stmt.G == stmt.X);
    assert!(wit * stmt.A == stmt.B);

    let mut rng = OsRng;
    let r = Scalar::random(&mut rng);
    let R1 = r * stmt.G;
    let R2 = r * stmt.A;

    trans.append_message(b"G", stmt.G.compress().as_bytes());
    trans.append_message(b"X", stmt.X.compress().as_bytes());
    trans.append_message(b"A", stmt.A.compress().as_bytes());
    trans.append_message(b"B", stmt.B.compress().as_bytes());
    trans.append_message(b"R_1", R1.compress().as_bytes());
    trans.append_message(b"R_2", R2.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);
    let s = r + c * wit;

    DleqProof { c, s }
}

pub fn verify_dleq(
    trans: &mut Transcript,
    proof: &DleqProof,
    stmt: &DleqStatement,
) -> bool {
    // recompute the R:
    // R1 = s * G - c * X
    // R2 = s * A - c * B
    let R1 = proof.s * stmt.G - proof.c * stmt.X;
    let R2 = proof.s * stmt.A - proof.c * stmt.B;

    trans.append_message(b"G", stmt.G.compress().as_bytes());
    trans.append_message(b"X", stmt.X.compress().as_bytes());
    trans.append_message(b"A", stmt.A.compress().as_bytes());
    trans.append_message(b"B", stmt.B.compress().as_bytes());
    trans.append_message(b"R_1", R1.compress().as_bytes());
    trans.append_message(b"R_2", R2.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);

    c == proof.c
}
