use curve25519_dalek::{RistrettoPoint, Scalar};
use merlin::Transcript;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};

pub struct LinkCommitWitness {
    pub a: Scalar, // ephemeral secret
    pub m: Scalar, // root (tag) of tree
    pub r: Scalar, // commitment randomness
}

/// The statement of commitment link:
/// (C1 = a * G1 - m * G2) & (C2 = r * H1 + m * H2)
pub struct LinkCommitStatement {
    pub C1: RistrettoPoint,
    pub G1: RistrettoPoint,
    pub G2: RistrettoPoint,
    pub C2: RistrettoPoint,
    pub H1: RistrettoPoint,
    pub H2: RistrettoPoint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LinkCommitProof {
    pub c: Scalar,
    pub s1: Scalar,
    pub s2: Scalar,
    pub s3: Scalar,
}

pub fn prove_commit_link(
    trans: &mut Transcript,
    wit: &LinkCommitWitness,
    stmt: &LinkCommitStatement,
) -> LinkCommitProof {
    // Ensure the witness is valid
    assert!(wit.a * stmt.G1 - wit.m * stmt.G2 == stmt.C1);
    assert!(wit.r * stmt.H1 + wit.m * stmt.H2 == stmt.C2);

    let mut rng = OsRng;
    let r1 = Scalar::random(&mut rng);
    let r2 = Scalar::random(&mut rng);
    let r3 = Scalar::random(&mut rng);

    // R1 = r1 * H1 + r2 * H2
    // R2 = (-r1) * G1 + r2 * G2
    let R1 = r1 * stmt.H1 + r2 * stmt.H2;
    let R2 = (-r1) * stmt.G1 + r2 * stmt.G2;

    trans.append_message(b"C_1", stmt.C1.compress().as_bytes());
    trans.append_message(b"G_1", stmt.G1.compress().as_bytes());
    trans.append_message(b"G_2", stmt.G2.compress().as_bytes());
    trans.append_message(b"C_2", stmt.C2.compress().as_bytes());
    trans.append_message(b"H_1", stmt.H1.compress().as_bytes());
    trans.append_message(b"H_2", stmt.H2.compress().as_bytes());
    trans.append_message(b"R_1", R1.compress().as_bytes());
    trans.append_message(b"R_2", R2.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);
    let s1 = r1 + c * wit.m;
    let s2 = r2 + c * wit.r;
    let s3 = r3 + c * wit.a;

    LinkCommitProof { c, s1, s2, s3 }
}

pub fn verify_commit_link(
    trans: &mut Transcript,
    proof: &LinkCommitProof,
    stmt: &LinkCommitStatement,
) -> bool {
    // recompute the R:
    // R1 = s1 * H1 + s2 * H2 - c * C2
    // R2 = (-s1) * G1 + s3 * G2 - c * C1
    let R1 = proof.s1 * stmt.H1 + proof.s2 * stmt.H2 - proof.c * stmt.C2;
    let R2 = (-proof.s1) * stmt.G1 + proof.s3 * stmt.G2 - proof.c * stmt.C1;

    trans.append_message(b"C_1", stmt.C1.compress().as_bytes());
    trans.append_message(b"G_1", stmt.G1.compress().as_bytes());
    trans.append_message(b"G_2", stmt.G2.compress().as_bytes());
    trans.append_message(b"C_2", stmt.C2.compress().as_bytes());
    trans.append_message(b"H_1", stmt.H1.compress().as_bytes());
    trans.append_message(b"H_2", stmt.H2.compress().as_bytes());
    trans.append_message(b"R_1", R1.compress().as_bytes());
    trans.append_message(b"R_2", R2.compress().as_bytes());

    let mut challenge_bytes = [0u8; 64];
    trans.challenge_bytes(b"c", &mut challenge_bytes);

    let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);

    c == proof.c
}
