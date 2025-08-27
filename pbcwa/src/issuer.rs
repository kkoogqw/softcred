use std::fmt::Error;

use curve25519_dalek::{RistrettoPoint, Scalar};
use gadgets::{
    get_poseison_parameters,
    poseidon::{builder::Poseidon, sbox::PoseidonSbox},
};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

use crate::{
    credential::{
        AuthenticationToken, BlindTransformUserMessage1,
        BlindTransformUserMessage2, Credential,
    },
    utils::{
        attribute_tree::{Attribute, AttributeTree},
        nizk_dlog,
    },
    verifier,
};

pub type SecretKey = Scalar;
pub type VerificationKey = RistrettoPoint;

#[derive(Debug, Clone)]
pub struct Parameters {
    pub G: RistrettoPoint,
    pub CRH: Poseidon,
    pub vk: VerificationKey,
}

pub type IssueSecretKey = Scalar;

#[derive(Debug, Clone)]
pub struct Issuer {
    pub params: Parameters,
    pub secret: IssueSecretKey,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlindTransformIssuerMessage1 {
    pub R1: RistrettoPoint,
    pub R2: RistrettoPoint,
    pub V: RistrettoPoint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlindTransformIssuerMessage2 {
    pub s: Scalar,
}

pub struct BlindTransformState {
    pub r: Scalar,
}

impl Issuer {
    pub fn new() -> Self {
        let mut rng = rand::thread_rng();
        let G = RistrettoPoint::random(&mut rng);
        let CRH = get_poseison_parameters(Some(PoseidonSbox::Exponentiation17));
        let sk = Scalar::random(&mut rng);
        let vk = sk * G;

        let params = Parameters { G, CRH, vk };

        Self { params, secret: sk }
    }

    pub fn get_parameters(self) -> Parameters { self.params }

    pub fn issue(
        self,
        tag: Scalar,
    ) -> Result<Credential, Error> {
        // The attribute tree is pre-built.
        // let mut tree = AttributeTree::new(self.params.CRH.clone());
        // tree.build(attributes);
        // let tag = tree.get_root();

        if (tag == Scalar::ZERO || tag == self.secret) {
            return Err(Error);
        }

        // compute the credential cred = (sk + m)^(-1) * G
        let cred = (tag + self.secret).invert() * self.params.G;

        Ok(Credential { tag, cred })
    }

    pub fn blind_transform_issuer_response(
        &self,
        message: &BlindTransformUserMessage1,
        nonce: &[u8; 32],
    ) -> Result<(BlindTransformIssuerMessage1, BlindTransformState), Error>
    {
        // compute: U = (sk + m) * T
        let U = (self.secret + message.token.tag) * message.token.rand_cred;

        // verify the proof:
        let stmt = nizk_dlog::DlogStatement {
            G: self.params.G,
            X: U,
        };
        let mut verifier_trans = Transcript::new(b"blind_transform_request");
        verifier_trans.append_message(
            b"T",
            message.token.rand_cred.compress().as_bytes(),
        );
        verifier_trans.append_message(b"nonce", nonce);

        let verify = nizk_dlog::verify_dlog(
            &mut verifier_trans,
            &message.token.proof,
            &stmt,
        );

        if verify == false {
            return Err(Error);
        }

        // sample r for public verifiability
        let mut rng = rand::thread_rng();
        let r = Scalar::random(&mut rng);
        let R1 = r * self.params.G;
        let R2 = r * message.token.rand_cred;
        let V = self.secret * message.token.rand_cred;

        let message = BlindTransformIssuerMessage1 { R1, R2, V };
        let state = BlindTransformState { r };

        Ok((message, state))
    }

    pub fn blind_transform_issuer_finalize(
        &self,
        message: &BlindTransformUserMessage2,
        state: &BlindTransformState,
    ) -> Result<BlindTransformIssuerMessage2, Error> {
        // compute s: s = r + c * sk
        let s = state.r + message.c * self.secret;

        Ok(BlindTransformIssuerMessage2 { s })
    }
}
