use curve25519_dalek::{RistrettoPoint, Scalar};
use merlin::Transcript;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};

pub type CredentialWitness = Scalar;

/// The statement for proving well-form of issued credential:
/// (x * G = X) & (x * A = G - m * A)
pub struct CredentialStatement {
    pub G: RistrettoPoint,
    pub X: RistrettoPoint,
    pub A: RistrettoPoint, // issued credential
    pub m: Scalar,         // root of user's attribute tree.
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CredentialProof {
    pub c: Scalar,
    pub s: Scalar,
}

pub fn prove_credential(
    trans: &mut Transcript,
    wit: &CredentialWitness,
    stmt: &CredentialStatement,
) -> CredentialProof {
    // Ensure the witness is valid
    assert!(wit * stmt.G == stmt.X);
    assert!(wit * stmt.A == stmt.G - stmt.m * stmt.A);

    let mut rng = OsRng;
    let r = Scalar::random(&mut rng);
    let R1 = r * stmt.G;
    let R2 = r * stmt.A;

    trans.append_message(b"G", stmt.G.compress().as_bytes());
    trans.append_message(b"X", stmt.X.compress().as_bytes());
    trans.append_message(b"A", stmt.A.compress().as_bytes());
    trans.append_message(b"m", stmt.m.to_bytes().as_ref());
    trans.append_message(b"R_1", R1.compress().as_bytes());
    trans.append_message(b"R_2", R2.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);
    let s = r + c * wit;

    CredentialProof { c, s }
}

pub fn verify_credential(
    trans: &mut Transcript,
    proof: &CredentialProof,
    stmt: &CredentialStatement,
) -> bool {
    // recompute the R:
    // R1 = s * G - c * X
    // R2 = s * A - c * m
    let R1 = proof.s * stmt.G - proof.c * stmt.X;
    let R2 = (proof.s + proof.c * stmt.m) * stmt.A - proof.c * stmt.A;

    trans.append_message(b"G", stmt.G.compress().as_bytes());
    trans.append_message(b"X", stmt.X.compress().as_bytes());
    trans.append_message(b"A", stmt.A.compress().as_bytes());
    trans.append_message(b"m", stmt.m.to_bytes().as_ref());
    trans.append_message(b"R_1", R1.compress().as_bytes());
    trans.append_message(b"R_2", R2.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);

    c == proof.c
}
