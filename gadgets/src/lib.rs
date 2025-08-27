pub mod merkle_tree;
pub mod poseidon;
pub mod range;
pub mod smt;
pub mod utils;
pub mod zero_nonzero;

use crate::{
    poseidon::{
        allocate_statics_for_prover, allocate_statics_for_verifier,
        builder::{Poseidon, PoseidonBuilder},
        sbox::PoseidonSbox,
        Poseidon_hash_4, Poseidon_hash_4_gadget, Poseidon_permutation,
    },
    range::{count_bits, positive_no_gadget},
    smt::{
        builder::SparseMerkleTreeBuilder, vanilla_merkle_tree_verif_gadget,
        DEFAULT_TREE_DEPTH,
    },
    utils::{
        r1cs::{constrain_lc_with_scalar, AllocatedQuantity, AllocatedScalar},
        scalar::{get_bits, get_scalar_from_hex},
    },
};
use bulletproofs::{
    r1cs::{Prover, R1CSError, Verifier},
    BulletproofGens, PedersenGens,
};
use curve25519_dalek::Scalar;
use group::ff::Field;
use merlin::Transcript;
use rand_chacha::ChaChaRng;
use rand_core::SeedableRng;

pub fn add(left: u64, right: u64) -> u64 { left + right }

pub fn get_poseison_parameters(sbox: Option<PoseidonSbox>) -> Poseidon {
    let width = 6;
    let sbox = sbox.unwrap_or_else(|| PoseidonSbox::Inverse);

    let builder = PoseidonBuilder::new(width).sbox(sbox);
    let poseidon = builder.build();
    poseidon
}

pub fn test_poseidon_4to1(params: Poseidon, inputs: Vec<Scalar>) -> Scalar {
    let _width = params.width;
    let total_rounds = params.get_total_rounds();
    let mut _input = [Scalar::ZERO; 4];
    _input.copy_from_slice(inputs.as_slice());
    let expected_output = Poseidon_hash_4(_input, &params);

    expected_output
}

pub fn test_poseidon_bulletproofs(
    s_params: Poseidon,
    transcript_label: &'static [u8],
) {
    let _width = s_params.width;
    let total_rounds = s_params.get_total_rounds();

    let mut test_rng = ChaChaRng::from_seed([1u8; 32]);
    let _input = (0..4)
        .map(|_| Scalar::random(&mut test_rng))
        .collect::<Vec<_>>();
    let mut input = [Scalar::ZERO; 4];
    input.copy_from_slice(_input.as_slice());

    let start = std::time::Instant::now();
    let expected_output = Poseidon_hash_4(input, &s_params);
    let digest_time = start.elapsed();

    println!("Input:\n");
    for i in 0..4 {
        println!("x{}={:?}", i, &input[i]);
    }
    println!("Expected output:\n");
    println!("{:?}", &expected_output);
    println!("Time for digest-4To1: {:?}.", digest_time);

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(2048, 1);

    println!("Proving");
    let (proof, commitments) = {
        let mut prover_transcript = Transcript::new(transcript_label);
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let mut comms = vec![];
        let mut allocs = vec![];

        for inp in input.iter() {
            let (com, var) =
                prover.commit(inp.clone(), Scalar::random(&mut test_rng));
            comms.push(com);
            allocs.push(AllocatedScalar {
                variable: var,
                assignment: Some(inp.clone()),
            });
        }

        let num_statics = 2;
        let statics = allocate_statics_for_prover(&mut prover, num_statics);

        let start = std::time::Instant::now();
        assert!(Poseidon_hash_4_gadget(
            &mut prover,
            allocs,
            statics,
            &s_params,
            &expected_output
        )
        .is_ok());

        println!(
            "For Poseidon hash 4:1 rounds {}, no of constraints is {}, no of
        multipliers is {}",
            total_rounds,
            &prover.num_constraints(),
            &prover.num_multipliers()
        );

        let proof = prover.prove(&bp_gens).unwrap();
        let end = start.elapsed();

        println!("Proving time is {:?}, Sbox: {:?}", end, s_params.sbox);
        (proof, comms)
    };

    // print size of proof
    let serded_proof = bincode::serialize(&proof).unwrap();
    println!("Size of proof: {} bytes", serded_proof.len());

    let decoded_proof: bulletproofs::r1cs::R1CSProof =
        bincode::deserialize(&serded_proof).unwrap();

    println!("Verifying");

    let mut verifier_transcript = Transcript::new(transcript_label);
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let mut allocs = vec![];
    for com in commitments {
        let v = verifier.commit(com);
        allocs.push({
            AllocatedScalar {
                variable: v,
                assignment: None,
            }
        });
    }

    let num_statics = 2;
    let statics =
        allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

    let start = std::time::Instant::now();
    assert!(Poseidon_hash_4_gadget(
        &mut verifier,
        allocs,
        statics,
        &s_params,
        &expected_output
    )
    .is_ok());

    assert!(verifier.verify(&decoded_proof, &pc_gens, &bp_gens).is_ok());
    let end = start.elapsed();

    println!("Verification time is {:?}, Sbox: {:?}", end, s_params.sbox);
}

pub fn test_merkle_tree_bulletproof() {
    let mut test_rng = ChaChaRng::from_seed([1u8; 32]);

    let width = 6;
    let p_params = PoseidonBuilder::new(width)
        .sbox(PoseidonSbox::Inverse)
        .build();

    let mut tree = SparseMerkleTreeBuilder::new()
        .hash_params(p_params.clone())
        .build();

    for i in 1..16 {
        let s = Scalar::from(i as u32);
        tree.update(s, s);
    }


    let start = std::time::Instant::now();
    let mut merkle_proof_vec = Vec::<Scalar>::new();
    let mut merkle_proof = Some(merkle_proof_vec);
    let k = Scalar::from(7u32);
    assert_eq!(k, tree.get(k, tree.root, &mut merkle_proof));
    merkle_proof_vec = merkle_proof.unwrap();
    assert!(tree.verify_proof(k, k, &merkle_proof_vec, None));
    assert!(tree.verify_proof(k, k, &merkle_proof_vec, Some(&tree.root)));
    let duration = start.elapsed();
    println!(
        "Time taken to generate and verify Merkle path-proof: {:?}",
        duration
    );

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(16500, 1);

    let (proof, commitments) = {
        let mut prover_transcript = Transcript::new(b"VSMT");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (com_leaf, var_leaf) =
            prover.commit(k, Scalar::random(&mut test_rng));
        let leaf_alloc_scalar = AllocatedScalar {
            variable: var_leaf,
            assignment: Some(k),
        };

        let mut leaf_index_comms = vec![];
        let mut leaf_index_vars = vec![];
        let mut leaf_index_alloc_scalars = vec![];
        for b in get_bits(&k, DEFAULT_TREE_DEPTH).iter().take(tree.depth) {
            let val: Scalar = Scalar::from(*b as u8);
            let (c, v) =
                prover.commit(val.clone(), Scalar::random(&mut test_rng));
            leaf_index_comms.push(c);
            leaf_index_vars.push(v);
            leaf_index_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: Some(val),
            });
        }

        let mut proof_comms = vec![];
        let mut proof_vars = vec![];
        let mut proof_alloc_scalars = vec![];
        for p in merkle_proof_vec.iter() {
            let (c, v) = prover.commit(*p, Scalar::random(&mut test_rng));
            proof_comms.push(c);
            proof_vars.push(v);
            proof_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: Some(*p),
            });
        }

        let num_statics = 4;
        let statics = allocate_statics_for_prover(&mut prover, num_statics);

        let start = std::time::Instant::now();
        assert!(vanilla_merkle_tree_verif_gadget(
            &mut prover,
            tree.depth,
            &tree.root,
            leaf_alloc_scalar,
            leaf_index_alloc_scalars,
            proof_alloc_scalars,
            statics,
            &p_params
        )
        .is_ok());

        //            println!("For tree height {} and MiMC rounds {}, no of
        // constraints is {}", tree.depth, &MIMC_ROUNDS,
        // &prover.num_constraints());

        println!(
			"For binary tree of height {}, no of multipliers is {} and constraints is {}",
			tree.depth,
			&prover.num_multipliers(),
			&prover.num_constraints()
		);

        let proof = prover.prove(&bp_gens).unwrap();
        let end = start.elapsed();

        println!("Proving time is {:?}, sbox: {:?}", end, p_params.sbox);

        (proof, (com_leaf, leaf_index_comms, proof_comms))
    };

    // print size of proofs
    println!("Size of proofs: {}", proof.serialized_size());
    println!(
        "num of commitments: {}",
        commitments.1.len() + commitments.2.len() + 1
    );

    let mut verifier_transcript = Transcript::new(b"VSMT");
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let var_leaf = verifier.commit(commitments.0);
    let leaf_alloc_scalar = AllocatedScalar {
        variable: var_leaf,
        assignment: None,
    };

    let mut leaf_index_alloc_scalars = vec![];
    for l in commitments.1 {
        let v = verifier.commit(l);
        leaf_index_alloc_scalars.push(AllocatedScalar {
            variable: v,
            assignment: None,
        });
    }

    let mut proof_alloc_scalars = vec![];
    for p in commitments.2 {
        let v = verifier.commit(p);
        proof_alloc_scalars.push(AllocatedScalar {
            variable: v,
            assignment: None,
        });
    }

    let num_statics = 4;
    let statics =
        allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

    let start = std::time::Instant::now();
    assert!(vanilla_merkle_tree_verif_gadget(
        &mut verifier,
        tree.depth,
        &tree.root,
        leaf_alloc_scalar,
        leaf_index_alloc_scalars,
        proof_alloc_scalars,
        statics,
        &p_params
    )
    .is_ok());

    assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    let end = start.elapsed();

    println!("Verification time is {:?}, sbox: {:?}", end, p_params.sbox);
}

pub fn test_range_proof_gadget() {
    use rand::{rngs::OsRng, Rng};

    let mut rng: OsRng = OsRng::default();
    // let min = 100000000000;
    // let max = 200000000000;
    // let v = 158600000000;

    let min = 1000000;
    let max = 2000000;

    let v = 1586000;

    println!("v is {}", &v);
    assert!(range_proof_helper(v, min, max).is_ok());
}

fn range_proof_helper(v: u64, min: u64, max: u64) -> Result<(), R1CSError> {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let n = count_bits(max);
    println!("bit_size is {}", &n);

    let a = v - min;
    let b = max - v;
    println!("a, b are {} {}", &a, &b);

    // Prover's scope
    let start = std::time::Instant::now();
    let (proof, commitments) = {
        let mut comms = vec![];

        // Prover makes a `ConstraintSystem` instance representing a range proof
        // gadget
        let mut prover_transcript = Transcript::new(b"BoundsTest");
        let mut rng = rand::thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        // Constrain a in [0, 2^n)
        let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: Some(a),
        };
        assert!(positive_no_gadget(&mut prover, quantity_a, n).is_ok());
        comms.push(com_a);

        // Constrain b in [0, 2^n)
        let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: Some(b),
        };
        assert!(positive_no_gadget(&mut prover, quantity_b, n).is_ok());
        comms.push(com_b);

        // Constrain a+b to be same as max-min. This ensures same v is used in
        // both commitments (`com_a` and `com_b`)
        constrain_lc_with_scalar(
            &mut prover,
            var_a + var_b,
            &(max - min).into(),
        );

        println!(
            "For {} in ({}, {}), no of constraints is {}",
            v,
            min,
            max,
            &prover.num_constraints()
        );
        // println!("Prover commitments {:?}", &comms);
        let proof = prover.prove(&bp_gens)?;

        (proof, comms)
    };
    let duration = start.elapsed();
    println!("Proving done");
    println!("Proving time: {:?}", duration);
    println!("Size of proof: {} bytes", proof.serialized_size());
    println!("Number of commitments: {}", commitments.len());

    // Verifier makes a `ConstraintSystem` instance representing a merge gadget
    let mut verifier_transcript = Transcript::new(b"BoundsTest");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let var_a = verifier.commit(commitments[0]);
    let quantity_a = AllocatedQuantity {
        variable: var_a,
        assignment: None,
    };
    assert!(positive_no_gadget(&mut verifier, quantity_a, n).is_ok());

    let var_b = verifier.commit(commitments[1]);
    let quantity_b = AllocatedQuantity {
        variable: var_b,
        assignment: None,
    };
    assert!(positive_no_gadget(&mut verifier, quantity_b, n).is_ok());

    //        println!("Verifier commitments {:?}", &commitments);

    constrain_lc_with_scalar(&mut verifier, var_a + var_b, &(max - min).into());

    // Verifier verifies proof
    println!("Verifying...");

    let start = std::time::Instant::now();
    let res = verifier.verify(&proof, &pc_gens, &bp_gens).is_ok();
    let end = start.elapsed();
    println!("Verify result: {}", res);
    println!("Verification time: {:?}", end);

    Ok(())
}

#[cfg(test)]
mod tests {
    use serde::Serialize;

    use crate::{
        smt::{
            builder::SparseMerkleTreeBuilder, vanilla_merkle_tree_verif_gadget,
            DEFAULT_TREE_DEPTH,
        },
        utils::scalar::get_bits,
    };

    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        println!("Result of add(2, 2): {}", result);
        assert_eq!(result, 4);
    }

    fn get_poseidon_params(sbox: Option<PoseidonSbox>) -> Poseidon {
        let width = 6;
        let sbox = sbox.unwrap_or_else(|| PoseidonSbox::Inverse);

        let builder = PoseidonBuilder::new(width).sbox(sbox);
        let poseidon = builder.build();
        poseidon
    }

    fn poseidon_perm(
        s_params: Poseidon,
        transcript_label: &'static [u8],
    ) -> Vec<Scalar> {
        let width = s_params.width;
        let total_rounds = s_params.get_total_rounds();

        let mut test_rng = ChaChaRng::from_seed([1u8; 32]);
        let input = (0..width)
            .map(|_| Scalar::random(&mut test_rng))
            .collect::<Vec<_>>();
        let expected_output = Poseidon_permutation(&input, &s_params);

        expected_output
    }

    fn poseidon_hash_4(s_params: Poseidon, transcript_label: &'static [u8]) {
        let _width = s_params.width;
        let total_rounds = s_params.get_total_rounds();

        let mut test_rng = ChaChaRng::from_seed([1u8; 32]);
        let _input = (0..4)
            .map(|_| Scalar::random(&mut test_rng))
            .collect::<Vec<_>>();
        let mut input = [Scalar::ZERO; 4];
        input.copy_from_slice(_input.as_slice());

        let start = std::time::Instant::now();
        let expected_output = Poseidon_hash_4(input, &s_params);
        let digest_time = start.elapsed();

        println!("Input:\n");
        for i in 0..4 {
            println!("x{}={:?}", i, &input[i]);
        }
        println!("Expected output:\n");
        println!("{:?}", &expected_output);
        println!("Time for digest-4To1: {:?}.", digest_time);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        println!("Proving");
        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let mut comms = vec![];
            let mut allocs = vec![];

            for inp in input.iter() {
                let (com, var) =
                    prover.commit(inp.clone(), Scalar::random(&mut test_rng));
                comms.push(com);
                allocs.push(AllocatedScalar {
                    variable: var,
                    assignment: Some(inp.clone()),
                });
            }

            let num_statics = 2;
            let statics = allocate_statics_for_prover(&mut prover, num_statics);

            let start = std::time::Instant::now();
            assert!(Poseidon_hash_4_gadget(
                &mut prover,
                allocs,
                statics,
                &s_params,
                &expected_output
            )
            .is_ok());

            println!(
        	"For Poseidon hash 4:1 rounds {}, no of constraints is {}, no of
        multipliers is {}", 	total_rounds,
        	&prover.num_constraints(),
        	&prover.num_multipliers()
        );

            let proof = prover.prove(&bp_gens).unwrap();
            let end = start.elapsed();

            println!("Proving time is {:?}, Sbox: {:?}", end, s_params.sbox);
            (proof, comms)
        };

        println!("Verifying");

        let mut verifier_transcript = Transcript::new(transcript_label);
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let mut allocs = vec![];
        for com in commitments {
            let v = verifier.commit(com);
            allocs.push({
                AllocatedScalar {
                    variable: v,
                    assignment: None,
                }
            });
        }

        let num_statics = 2;
        let statics =
            allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

        let start = std::time::Instant::now();
        assert!(Poseidon_hash_4_gadget(
            &mut verifier,
            allocs,
            statics,
            &s_params,
            &expected_output
        )
        .is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        let end = start.elapsed();

        println!("Verification time is {:?}, Sbox: {:?}", end, s_params.sbox);
    }

    #[test]
    fn test_poseidon() {
        let par = get_poseidon_params(Some(PoseidonSbox::Exponentiation3));
        let perm_digest = poseidon_perm(par.clone(), b"test_label");

        println!("Digest-permutation: {:?}", perm_digest);

        // hash 4-input
        let dig = poseidon_hash_4(par.clone(), b"test_label");
    }

    #[test]
    fn test_merkle_tree() {
        let mut test_rng = ChaChaRng::from_seed([1u8; 32]);

        let width = 6;
        let p_params = PoseidonBuilder::new(width)
            .sbox(PoseidonSbox::Inverse)
            .build();

        let mut tree = SparseMerkleTreeBuilder::new()
            .hash_params(p_params.clone())
            .build();

        for i in 1..16 {
            let s = Scalar::from(i as u32);
            tree.update(s, s);
        }

        let mut merkle_proof_vec = Vec::<Scalar>::new();
        let mut merkle_proof = Some(merkle_proof_vec);
        let k = Scalar::from(7u32);
        assert_eq!(k, tree.get(k, tree.root, &mut merkle_proof));
        merkle_proof_vec = merkle_proof.unwrap();
        assert!(tree.verify_proof(k, k, &merkle_proof_vec, None));
        assert!(tree.verify_proof(k, k, &merkle_proof_vec, Some(&tree.root)));

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16500, 1);

        let (proof, commitments) = {
            let mut prover_transcript = Transcript::new(b"VSMT");
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

            let (com_leaf, var_leaf) =
                prover.commit(k, Scalar::random(&mut test_rng));
            let leaf_alloc_scalar = AllocatedScalar {
                variable: var_leaf,
                assignment: Some(k),
            };

            let mut leaf_index_comms = vec![];
            let mut leaf_index_vars = vec![];
            let mut leaf_index_alloc_scalars = vec![];
            for b in get_bits(&k, DEFAULT_TREE_DEPTH).iter().take(tree.depth) {
                let val: Scalar = Scalar::from(*b as u8);
                let (c, v) =
                    prover.commit(val.clone(), Scalar::random(&mut test_rng));
                leaf_index_comms.push(c);
                leaf_index_vars.push(v);
                leaf_index_alloc_scalars.push(AllocatedScalar {
                    variable: v,
                    assignment: Some(val),
                });
            }

            let mut proof_comms = vec![];
            let mut proof_vars = vec![];
            let mut proof_alloc_scalars = vec![];
            for p in merkle_proof_vec.iter() {
                let (c, v) = prover.commit(*p, Scalar::random(&mut test_rng));
                proof_comms.push(c);
                proof_vars.push(v);
                proof_alloc_scalars.push(AllocatedScalar {
                    variable: v,
                    assignment: Some(*p),
                });
            }

            let num_statics = 4;
            let statics = allocate_statics_for_prover(&mut prover, num_statics);

            let start = std::time::Instant::now();
            assert!(vanilla_merkle_tree_verif_gadget(
                &mut prover,
                tree.depth,
                &tree.root,
                leaf_alloc_scalar,
                leaf_index_alloc_scalars,
                proof_alloc_scalars,
                statics,
                &p_params
            )
            .is_ok());

            //            println!("For tree height {} and MiMC rounds {}, no of
            // constraints is {}", tree.depth, &MIMC_ROUNDS,
            // &prover.num_constraints());

            println!(
			"For binary tree of height {}, no of multipliers is {} and constraints is {}",
			tree.depth,
			&prover.num_multipliers(),
			&prover.num_constraints()
		);

            let proof = prover.prove(&bp_gens).unwrap();
            let end = start.elapsed();

            println!("Proving time is {:?}, sbox: {:?}", end, p_params.sbox);

            (proof, (com_leaf, leaf_index_comms, proof_comms))
        };

        // print size of proofs
        println!("Size of proofs: {}", proof.serialized_size());
        println!(
            "num of commitments: {}",
            commitments.1.len() + commitments.2.len() + 1
        );

        let mut verifier_transcript = Transcript::new(b"VSMT");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let var_leaf = verifier.commit(commitments.0);
        let leaf_alloc_scalar = AllocatedScalar {
            variable: var_leaf,
            assignment: None,
        };

        let mut leaf_index_alloc_scalars = vec![];
        for l in commitments.1 {
            let v = verifier.commit(l);
            leaf_index_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }

        let mut proof_alloc_scalars = vec![];
        for p in commitments.2 {
            let v = verifier.commit(p);
            proof_alloc_scalars.push(AllocatedScalar {
                variable: v,
                assignment: None,
            });
        }

        let num_statics = 4;
        let statics =
            allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

        let start = std::time::Instant::now();
        assert!(vanilla_merkle_tree_verif_gadget(
            &mut verifier,
            tree.depth,
            &tree.root,
            leaf_alloc_scalar,
            leaf_index_alloc_scalars,
            proof_alloc_scalars,
            statics,
            &p_params
        )
        .is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        let end = start.elapsed();

        println!("Verification time is {:?}, sbox: {:?}", end, p_params.sbox);
    }
}
