use bulletproofs::r1cs::R1CSProof;
use curve25519_dalek::{RistrettoPoint, Scalar};
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use sha2::Sha512;
use std::fmt::Error;

use crate::{
    issuer::{
        BlindTransformIssuerMessage1, BlindTransformIssuerMessage2, Parameters,
    },
    utils::{
        attribute_tree::AttributeTree,
        nizk_dleq::{self, DleqProof},
        nizk_dlog::{self, DlogProof},
    },
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Credential {
    pub tag: Scalar,
    pub cred: RistrettoPoint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthenticationToken {
    pub tag: Scalar,
    pub rand_cred: RistrettoPoint,
    pub proof: DlogProof,
}

pub type EphemeralSecret = Scalar;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PublicVerifiableToken {
    pub T: RistrettoPoint,
    pub V: RistrettoPoint,
    pub proof: DleqProof,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PresentationToken {
    pub commitments: Vec<RistrettoPoint>,
    pub proof_V: PublicVerifiableToken,
    pub proof_P: R1CSProof,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlindTransformUserMessage1 {
    pub token: AuthenticationToken,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlindTransformUserMessage2 {
    pub c: Scalar,
}

pub struct PresentationState {
    pub alpha: Scalar,
    pub beta: Scalar,
    pub epsilon: Scalar,
    pub rho: Scalar,
    pub c: Scalar,
    pub s: Scalar,
    pub T: RistrettoPoint,
    pub V: RistrettoPoint,
}

pub struct PublicVerifiableTokenExt {
    pub G: RistrettoPoint,
    pub T: RistrettoPoint,
    pub V: RistrettoPoint,
    pub proof_V: DleqProof,
    pub proof_G: DlogProof,
}
pub struct PresentationTokenExt {
    pub commitments: Vec<RistrettoPoint>,
    pub proof_V: PublicVerifiableTokenExt,
    pub proof_P: R1CSProof,
}
pub struct PresentationStateExt {
    pub alpha: Scalar,
    pub beta: Scalar,
    pub gamma: Scalar,
    pub epsilon: Scalar,
    pub rho: Scalar,
    pub c: Scalar,
    pub s: Scalar,
    pub T: RistrettoPoint,
    pub V: RistrettoPoint,
    pub G: RistrettoPoint,
}

impl Credential {
    // pub fn new() {}

    pub fn encrypt(
        &self,
        params: Parameters,
        tag: Scalar,
        private_word: &String,
    ) -> Result<Credential, Error> {
        // The attribute tree is pre-built.
        // check the attributes is valid for tag:
        // let mut tree = AttributeTree::new(params.CRH);
        // tree.build(attributes);
        // let tag = tree.get_root();

        if (tag == Scalar::ZERO) || (tag != self.tag) {
            return Err(Error);
        }

        let mask_point =
            RistrettoPoint::hash_from_bytes::<Sha512>(private_word.as_bytes());
        let encrypted_cred = self.cred + mask_point;

        Ok(Credential {
            tag: self.tag,
            cred: encrypted_cred,
        })
    }

    pub fn update_encrypt(
        &self,
        old_private_word: String,
        new_private_word: String,
    ) -> Credential {
        let old_mask_point = RistrettoPoint::hash_from_bytes::<Sha512>(
            old_private_word.as_bytes(),
        );
        let new_mask_point = RistrettoPoint::hash_from_bytes::<Sha512>(
            new_private_word.as_bytes(),
        );
        let encrypted_cred = self.cred - old_mask_point + new_mask_point;

        Credential {
            tag: self.tag,
            cred: encrypted_cred,
        }
    }

    pub fn blind_transform_request(
        &self,
        params: Parameters,
        private_word: &String,
        nonce: &[u8; 32],
    ) -> Result<(BlindTransformUserMessage1, PresentationState), Error> {
        let masking =
            RistrettoPoint::hash_from_bytes::<Sha512>(private_word.as_bytes());

        let decrypted_cred = self.cred - masking;
        let mut rng = rand::thread_rng();
        let alpha = Scalar::random(&mut rng);
        let beta = Scalar::random(&mut rng);
        let a = alpha * beta;
        let T = a * decrypted_cred;
        let U = a * params.G;

        // Proof of knowledge of a:
        let mut prover_trans = Transcript::new(b"blind_transform_request");
        prover_trans.append_message(b"T", T.compress().as_bytes());
        prover_trans.append_message(b"nonce", nonce);

        // Generate proof
        let stmt = nizk_dlog::DlogStatement { G: params.G, X: U };
        // let wit = a;
        let proof = nizk_dlog::prove_dlog(&mut prover_trans, &a, &stmt);

        let state = PresentationState {
            alpha,
            beta,
            epsilon: Scalar::ZERO,
            rho: Scalar::ZERO,
            c: Scalar::ZERO,
            s: Scalar::ZERO,
            T: alpha * decrypted_cred,
            V: RistrettoPoint::default(),
        };

        let message = BlindTransformUserMessage1 {
            token: AuthenticationToken {
                tag: self.tag,
                rand_cred: T,
                proof,
            },
        };

        Ok((message, state))
    }

    pub fn blind_transform_user_response(
        &self,
        params: Parameters,
        state: &PresentationState,
        message: &BlindTransformIssuerMessage1,
    ) -> Result<(BlindTransformUserMessage2, PresentationState), Error> {
        // derandomize the message from issuer
        let _V = state.beta.invert() * message.V;
        let _T = state.T;

        let mut rng = rand::thread_rng();
        let epsilon = Scalar::random(&mut rng);
        let rho = Scalar::random(&mut rng);

        let _R1 = epsilon.invert() * message.R1 + rho * params.G;
        let _R2 = (epsilon.invert() * state.beta.invert()) * message.R2
            + rho * state.T;

        // Verify the response
        let mut prover_trans = Transcript::new(b"blind_transform_response");

        prover_trans.append_message(b"G", params.G.compress().as_bytes());
        prover_trans.append_message(b"X", params.vk.compress().as_bytes());
        prover_trans.append_message(b"A", _T.compress().as_bytes());
        prover_trans.append_message(b"B", _V.compress().as_bytes());
        prover_trans.append_message(b"R_1", _R1.compress().as_bytes());
        prover_trans.append_message(b"R_2", _R2.compress().as_bytes());

        let mut challenge_bytes = [0u8; 64];
        prover_trans.challenge_bytes(b"c", &mut challenge_bytes);

        let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);
        let _c = epsilon * c;

        let message = BlindTransformUserMessage2 { c: _c };
        let state = PresentationState {
            alpha: state.alpha,
            beta: Scalar::ZERO,
            epsilon,
            rho,
            c,
            s: Scalar::ZERO,
            T: _T,
            V: _V,
        };

        Ok((message, state))
    }

    pub fn blind_transform_user_finalize(
        &self,
        message: &BlindTransformIssuerMessage2,
        state: &PresentationState,
    ) -> Result<(EphemeralSecret, PublicVerifiableToken), Error> {
        // compute s
        let s = state.epsilon.invert() * message.s + state.rho;
        let proof = nizk_dleq::DleqProof { c: state.c, s };
        let token = PublicVerifiableToken {
            T: state.T,
            V: state.V,
            proof,
        };
        Ok((state.alpha, token))
    }

    pub fn blind_transform_ext_request(
        &self,
        params: Parameters,
        private_word: String,
        nonce: &[u8; 32],
    ) -> Result<(BlindTransformUserMessage1, PresentationStateExt), Error> {
        let masking =
            RistrettoPoint::hash_from_bytes::<Sha512>(private_word.as_bytes());

        let decrypted_cred = self.cred - masking;
        let mut rng = rand::thread_rng();
        let alpha = Scalar::random(&mut rng);
        let beta = Scalar::random(&mut rng);
        let gamma = Scalar::random(&mut rng);
        let a = alpha * beta * gamma;
        let T = a * decrypted_cred;
        let U = a * params.G;
        let G = gamma * params.G;

        // Proof of knowledge of a:
        let mut prover_trans = Transcript::new(b"blind_transform_request");
        prover_trans.append_message(b"T", T.compress().as_bytes());
        prover_trans.append_message(b"nonce", nonce);

        // Generate proof
        let stmt = nizk_dlog::DlogStatement { G: params.G, X: U };
        // let wit = a;
        let proof = nizk_dlog::prove_dlog(&mut prover_trans, &a, &stmt);

        let state = PresentationStateExt {
            alpha,
            beta,
            gamma,
            epsilon: Scalar::ZERO,
            rho: Scalar::ZERO,
            c: Scalar::ZERO,
            s: Scalar::ZERO,
            T: beta.invert() * T,
            V: RistrettoPoint::default(),
            G,
        };

        let message = BlindTransformUserMessage1 {
            token: AuthenticationToken {
                tag: self.tag,
                rand_cred: T,
                proof,
            },
        };

        Ok((message, state))
    }

    pub fn bilnd_transform_ext_user_response(
        &self,
        params: Parameters,
        state: &PresentationStateExt,
        message: &BlindTransformIssuerMessage1,
    ) -> Result<(BlindTransformUserMessage2, PresentationStateExt), Error> {
        // derandomize the message from issuer
        let _V = state.beta.invert() * message.V;
        let _T = state.T;

        let mut rng = rand::thread_rng();
        let epsilon = Scalar::random(&mut rng);
        let rho = Scalar::random(&mut rng);

        let _R1 = epsilon.invert() * message.R1 + rho * params.G;
        let _R2 = (epsilon.invert() * state.beta.invert()) * message.R2
            + rho * state.T;

        // Verify the response
        let mut prover_trans = Transcript::new(b"blind_transform_response");
        prover_trans.append_message(b"R1", _R1.compress().as_bytes());
        prover_trans.append_message(b"R2", _R2.compress().as_bytes());
        prover_trans.append_message(b"T", _T.compress().as_bytes());
        prover_trans.append_message(b"V", _V.compress().as_bytes());
        prover_trans.append_message(b"vk", params.vk.compress().as_bytes());

        let mut challenge_bytes = [0u8; 64];
        prover_trans.challenge_bytes(b"c", &mut challenge_bytes);

        let c = Scalar::from_bytes_mod_order_wide(&challenge_bytes);
        let _c = epsilon * c;

        let message = BlindTransformUserMessage2 { c: _c };
        let state = PresentationStateExt {
            alpha: state.alpha,
            beta: Scalar::ZERO,
            gamma: state.gamma,
            epsilon,
            rho,
            c,
            s: Scalar::ZERO,
            T: _T,
            V: _V,
            G: state.G,
        };

        Ok((message, state))
    }

    pub fn blind_transform_ext_user_finalize(
        &self,
        params: Parameters,
        message: &BlindTransformIssuerMessage2,
        state: &PresentationStateExt,
    ) -> Result<(EphemeralSecret, PublicVerifiableTokenExt), Error> {
        // compute s for pi_V
        let s = state.epsilon.invert() * message.s + state.rho;
        let proof_V = nizk_dleq::DleqProof { c: state.c, s };

        // build token with DLOG proof of G
        let stmt_G = nizk_dlog::DlogStatement {
            G: params.G,
            X: state.G,
        };
        let mut prover_trans =
            Transcript::new(b"blind_transform_rand_generator");
        prover_trans.append_message(b"T", state.T.compress().as_bytes());
        prover_trans.append_message(b"V", state.V.compress().as_bytes());
        // prover_trans.append_message(b"nonce", nonce);
        let proof_G =
            nizk_dlog::prove_dlog(&mut prover_trans, &state.gamma, &stmt_G);

        let token = PublicVerifiableTokenExt {
            G: state.G,
            T: state.T,
            V: state.V,
            proof_V,
            proof_G,
        };

        Ok((state.alpha, token))
    }

    pub fn preprocess_present(
        &self,
        attributes: Vec<Scalar>,
        policy: String,
    ) -> Result<(), Error> {
        Ok(())
    }

    pub fn present(
        &self,
        secret: &EphemeralSecret,
        pub_token: &PublicVerifiableToken,
    ) -> Result<(), Error> {
        Ok(())
    }

    pub fn present_ext() {}
}
