use std::borrow::BorrowMut;

use bincode::de;
use bulletproofs::{
    BulletproofGens, PedersenGens,
    r1cs::{
        ConstraintSystem, LinearCombination, Prover, R1CSError, R1CSProof,
        Variable, Verifier,
    },
};
use curve25519_dalek::{Scalar, ristretto::CompressedRistretto};
use gadgets::{
    poseidon::{
        self, Poseidon_hash_2_constraints, allocate_statics_for_prover,
        allocate_statics_for_verifier, builder::Poseidon,
    },
    range::{count_bits, positive_no_gadget},
    utils::{
        r1cs::{AllocatedQuantity, AllocatedScalar, constrain_lc_with_scalar},
        scalar::get_bits,
    },
};
use merlin::Transcript;
use rand_core::OsRng;

use crate::utils::attribute_tree::AttributeTree;

/// Attribute tree path verification gadget (single attribute disclosure)
pub fn attribute_tree_path_verify_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    root_var: AllocatedScalar, // hiddent root, witness
    leaf_public: Scalar,       // disclosed leaf
    leaf_index_bits_public: &[Scalar], // index of disclosed leaf
    proof_nodes: Vec<AllocatedScalar>, // hidden path, witness
    statics: Vec<AllocatedScalar>,
    poseidon_params: &Poseidon,
) -> Result<(), R1CSError> {
    let statics_lc: Vec<LinearCombination> =
        statics.iter().map(|s| s.variable.into()).collect();
    let mut prev_hash_opt = LinearCombination::default();

    for i in 0..depth {
        // the first layer uses the public constant leaf, and the subsequent
        // layers use the hash of the previous layer
        let cur_lc: LinearCombination = if i == 0 {
            // leaf => leaf * 1
            Variable::One() * leaf_public
        } else {
            prev_hash_opt.clone()
        };

        let bit = leaf_index_bits_public[i];
        let one_minus_bit = Scalar::ONE - bit;

        // left  = (1 - bit) * cur + bit * proof_i
        // right = bit * cur + (1 - bit) * proof_i
        let (_, _, left_1) =
            cs.multiply(Variable::One() * one_minus_bit, cur_lc.clone());
        let (_, _, left_2) =
            cs.multiply(Variable::One() * bit, proof_nodes[i].variable.into());
        let left = left_1 + left_2;

        let (_, _, right_1) = cs.multiply(Variable::One() * bit, cur_lc);
        let (_, _, right_2) = cs.multiply(
            Variable::One() * one_minus_bit,
            proof_nodes[i].variable.into(),
        );
        let right = right_1 + right_2;

        // constraints:  Poseidon(left, right)
        prev_hash_opt = Poseidon_hash_2_constraints::<CS>(
            cs,
            left,
            right,
            statics_lc.clone(),
            poseidon_params,
        )?;
    }

    // restrict the final hash to be equal to the hidden root variable
    cs.constrain(prev_hash_opt - root_var.variable);

    Ok(())
}

/// Composite proof circuit: Prove that the hidden leaf is in the hidden Merkle
/// tree and satisfies the range constraint x - leaf < y (i.e., leaf > x - y)
pub fn attribute_tree_path_verify_with_range_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    depth: usize,
    root_var: AllocatedScalar,         // hidden root
    leaf_var: AllocatedScalar,         // hidden leaf
    leaf_index_bits_public: &[Scalar], // idx
    proof_nodes: Vec<AllocatedScalar>, // hidden paths
    statics: Vec<AllocatedScalar>,     // Poseidon parameters
    poseidon_params: &Poseidon,
    x: u64, // range param x
    y: u64, // range param y
) -> Result<(), R1CSError> {
    use bulletproofs::r1cs::{LinearCombination, Variable};

    // Part 1: Merkle tree path verification
    let statics_lc: Vec<LinearCombination> =
        statics.iter().map(|s| s.variable.into()).collect();

    let mut prev_hash_opt: Option<LinearCombination> = None;

    for i in 0..depth {
        let cur_lc: LinearCombination = if i == 0 {
            leaf_var.variable.into()
        } else {
            prev_hash_opt.as_ref().unwrap().clone()
        };

        let bit = leaf_index_bits_public[i];
        let one_minus_bit = Scalar::ONE - bit;

        let (_, _, left_1) =
            cs.multiply(Variable::One() * one_minus_bit, cur_lc.clone());
        let (_, _, left_2) =
            cs.multiply(Variable::One() * bit, proof_nodes[i].variable.into());
        let left = left_1 + left_2;

        let (_, _, right_1) = cs.multiply(Variable::One() * bit, cur_lc);
        let (_, _, right_2) = cs.multiply(
            Variable::One() * one_minus_bit,
            proof_nodes[i].variable.into(),
        );
        let right = right_1 + right_2;

        let h = Poseidon_hash_2_constraints::<CS>(
            cs,
            left,
            right,
            statics_lc.clone(),
            poseidon_params,
        )?;
        prev_hash_opt = Some(h);
    }

    // the computed hash = root
    let prev_hash = prev_hash_opt.expect("depth must be > 0");
    cs.constrain(prev_hash - root_var.variable);

    // Part 2:  x < leaf < y
    // 1. leaf - x - 1 >= 0  (leaf > x)
    // 2. y - leaf - 1 >= 0  (leaf < y)
    // =>
    // 1. a = leaf - x - 1 in [0, 2^n)
    // 2. b = y - leaf - 1 in [0, 2^n)

    if x >= y {
        return Err(R1CSError::GadgetError {
            description: "Invalid range: x must be less than y".to_string(),
        });
    }

    //  leaf - x = delta1 (delta1 > 0)
    let (_, delta1_var, _) =
        cs.allocate_multiplier(leaf_var.assignment.map(|leaf_val| {
            let delta1 = leaf_val - Scalar::from(x);
            (Scalar::ONE, delta1)
        }))?;

    // delta1_var = leaf - x
    let delta1_lc = LinearCombination::from(leaf_var.variable)
        - Variable::One() * Scalar::from(x);
    cs.constrain(delta1_lc - delta1_var);

    // y - leaf = delta2 (delta2 > 0)
    let (_, delta2_var, _) =
        cs.allocate_multiplier(leaf_var.assignment.map(|leaf_val| {
            let delta2 = Scalar::from(y) - leaf_val;
            (Scalar::ONE, delta2)
        }))?;

    // delta2_var = y - leaf
    let delta2_lc = Variable::One() * Scalar::from(y)
        - LinearCombination::from(leaf_var.variable);
    cs.constrain(delta2_lc - delta2_var);

    // delta1 + delta2 = y - x
    let expected_range = Scalar::from(y - x);
    cs.constrain(
        LinearCombination::from(delta1_var)
            + LinearCombination::from(delta2_var)
            - Variable::One() * expected_range,
    );

    let range_size = y - x;
    let n = count_bits(range_size.max(1));

    // delta1 > 0  [1, 2^n)
    let delta1_minus_one =
        LinearCombination::from(delta1_var) - Variable::One();
    let (_, delta1_minus_one_var, _) =
        cs.allocate_multiplier(leaf_var.assignment.map(|leaf_val| {
            let delta1 = leaf_val - Scalar::from(x);
            let delta1_minus_one = delta1 - Scalar::ONE;
            (Scalar::ONE, delta1_minus_one)
        }))?;
    cs.constrain(delta1_minus_one - delta1_minus_one_var);

    let quantity_delta1 = AllocatedQuantity {
        variable: delta1_minus_one_var,
        assignment: leaf_var.assignment.map(|leaf_val| {
            let delta1_u64 = (leaf_val - Scalar::from(x) - Scalar::ONE)
                .to_bytes()
                .as_ref()
                .iter()
                .fold(0u64, |acc, &b| (acc << 8) | b as u64);
            delta1_u64
        }),
    };
    positive_no_gadget(cs, quantity_delta1, n)?;

    // delta2 > 0
    let delta2_minus_one =
        LinearCombination::from(delta2_var) - Variable::One();
    let (_, delta2_minus_one_var, _) =
        cs.allocate_multiplier(leaf_var.assignment.map(|leaf_val| {
            let delta2 = Scalar::from(y) - leaf_val;
            let delta2_minus_one = delta2 - Scalar::ONE;
            (Scalar::ONE, delta2_minus_one)
        }))?;
    cs.constrain(delta2_minus_one - delta2_minus_one_var);

    let quantity_delta2 = AllocatedQuantity {
        variable: delta2_minus_one_var,
        assignment: leaf_var.assignment.map(|leaf_val| {
            let delta2_u64 = (Scalar::from(y) - leaf_val - Scalar::ONE)
                .to_bytes()
                .as_ref()
                .iter()
                .fold(0u64, |acc, &b| (acc << 8) | b as u64);
            delta2_u64
        }),
    };
    positive_no_gadget(cs, quantity_delta2, n)?;

    Ok(())
}

pub fn generate_single_disclosure_proof<T: BorrowMut<Transcript>>(
    tree: &AttributeTree,
    leaf: Scalar,
    idx: usize,
    // pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    mut prover: Prover<T>,
) -> (
    R1CSProof,
    (CompressedRistretto, Vec<CompressedRistretto>),
    Scalar,
) {
    let mut rng = OsRng::default();
    let k = Scalar::from(idx as u64);
    let mut merkle_proof_vec = Vec::<Scalar>::new();
    let mut merkle_proof = Some(merkle_proof_vec);
    let _idx = tree.get(k, tree.root, &mut merkle_proof);
    if _idx != k {
        // handle the case where the index does not match
    }

    let merkle_proof_vec = merkle_proof.unwrap();

    // index bits
    let bits_bool = get_bits(&k, tree.depth);
    let bits_public: Vec<Scalar> = bits_bool
        .iter()
        .take(tree.depth)
        .map(|b| Scalar::from(*b as u8))
        .collect();

    // commit the root
    // NOTE: preserve the randomness here for SIGMA-protocol.
    let root_blinding = Scalar::random(&mut rng);
    let (com_root, var_root) = prover.commit(tree.root, root_blinding);
    let root_alloc_scalar = AllocatedScalar {
        variable: var_root,
        assignment: Some(tree.root),
    };

    // commit the proof nodes in path
    let mut proof_comms = vec![];
    let mut proof_alloc_scalars = vec![];
    for p in merkle_proof_vec.iter() {
        let (c, v) = prover.commit(*p, Scalar::random(&mut rng));
        proof_comms.push(c);
        proof_alloc_scalars.push(AllocatedScalar {
            variable: v,
            assignment: Some(*p),
        });
    }

    // Poseidon static parameters
    let num_statics = 4;
    let statics = allocate_statics_for_prover(&mut prover, num_statics);

    // constrain: from leaf to root
    attribute_tree_path_verify_gadget(
        &mut prover,
        tree.depth,
        root_alloc_scalar,
        leaf,
        &bits_public,
        proof_alloc_scalars,
        statics,
        &tree.hash_params,
    )
    .unwrap();
    println!("num of constraints: {:?}", &prover.num_constraints());

    let proof = prover.prove(bp_gens).unwrap();

    (proof, (com_root, proof_comms), root_blinding)
}

pub fn verify_single_disclosure_proof<T: BorrowMut<Transcript>>(
    tree_params: (usize, &Poseidon),
    leaf: Scalar,
    idx: usize,
    commitments: &(CompressedRistretto, Vec<CompressedRistretto>),
    proof: &R1CSProof,
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    mut verifier: Verifier<T>,
) -> Result<(), R1CSError> {
    let depth = tree_params.0;
    let poseidon = tree_params.1;
    let k = Scalar::from(idx as u64);
    let bits_bool = get_bits(&k, depth);
    let bits_public: Vec<Scalar> = bits_bool
        .iter()
        .take(depth)
        .map(|b| Scalar::from(*b as u8))
        .collect();

    let var_root = verifier.commit(commitments.0);
    let root_alloc = AllocatedScalar {
        variable: var_root,
        assignment: None,
    };

    let mut proof_allocs = vec![];
    for c in &commitments.1 {
        let v = verifier.commit(*c);
        proof_allocs.push(AllocatedScalar {
            variable: v,
            assignment: None,
        });
    }

    let num_statics = 4;
    let statics =
        allocate_statics_for_verifier(&mut verifier, num_statics, pc_gens);

    attribute_tree_path_verify_gadget(
        &mut verifier,
        depth,
        root_alloc,
        leaf,
        &bits_public,
        proof_allocs,
        statics,
        &poseidon,
    )?;

    verifier.verify(proof, pc_gens, bp_gens)?;

    Ok(())
}

pub fn generate_single_attribute_range_proof<T: BorrowMut<Transcript>>(
    tree: &AttributeTree,
    leaf: Scalar,
    idx: usize,
    x: u64,
    y: u64,
    // pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    mut prover: Prover<T>,
) -> Result<
    (
        R1CSProof,
        (
            CompressedRistretto,      // com_root
            CompressedRistretto,      // com_leaf
            Vec<CompressedRistretto>, // proof_comms path
        ),
        Scalar,
    ),
    R1CSError,
> {
    let mut rng = OsRng::default();

    if x >= y {
        return Err(R1CSError::GadgetError {
            description: format!(
                "Invalid range parameters: x={} must be less than y={}",
                x, y
            ),
        });
    }

    // check range constraint
    let leaf_bytes = leaf.as_bytes();
    let leaf_u64 = u64::from_le_bytes([
        leaf_bytes[0],
        leaf_bytes[1],
        leaf_bytes[2],
        leaf_bytes[3],
        leaf_bytes[4],
        leaf_bytes[5],
        leaf_bytes[6],
        leaf_bytes[7],
    ]);
    if leaf_u64 <= x || leaf_u64 >= y {
        return Err(R1CSError::GadgetError {
            description: format!(
                "Range constraint not satisfied: {} is not in ({}, {})",
                leaf_u64, x, y
            ),
        });
    }

    let delta1 = leaf - Scalar::from(x);
    let delta2 = Scalar::from(y) - leaf;

    if delta1 == Scalar::ZERO || delta2 == Scalar::ZERO {
        return Err(R1CSError::GadgetError {
            description: format!(
                "Strict inequality constraint not satisfied: leaf must be strictly between x and y"
            ),
        });
    }

    let k = Scalar::from(idx as u64);
    let bits_bool = get_bits(&k, tree.depth);
    let bits_public: Vec<Scalar> = bits_bool
        .iter()
        .take(tree.depth)
        .map(|b| Scalar::from(*b as u8))
        .collect();

    let mut merkle_proof_vec = Vec::<Scalar>::new();
    let mut merkle_proof = Some(merkle_proof_vec);
    let _idx = tree.get(k, tree.root, &mut merkle_proof);
    if _idx != k {
        // handle the case where the index does not match
    }

    let merkle_proof_vec = merkle_proof.unwrap();

    // NOTE: preserve the randomness of root commitment
    let root_blinding = Scalar::random(&mut rng);
    let (com_root, var_root) = prover.commit(tree.root, root_blinding);
    let root_alloc_scalar = AllocatedScalar {
        variable: var_root,
        assignment: Some(tree.root),
    };

    // commit the leaf
    let (com_leaf, var_leaf) = prover.commit(leaf, Scalar::random(&mut rng));
    let leaf_alloc_scalar = AllocatedScalar {
        variable: var_leaf,
        assignment: Some(leaf),
    };

    // commit the proof path
    let mut proof_comms = vec![];
    let mut proof_alloc_scalars = vec![];
    for p in merkle_proof_vec.iter() {
        let (c, v) = prover.commit(*p, Scalar::random(&mut rng));
        proof_comms.push(c);
        proof_alloc_scalars.push(AllocatedScalar {
            variable: v,
            assignment: Some(*p),
        });
    }

    // Poseidon parameters
    let num_statics = 4;
    let statics = allocate_statics_for_prover(&mut prover, num_statics);

    attribute_tree_path_verify_with_range_gadget(
        &mut prover,
        tree.depth,
        root_alloc_scalar,
        leaf_alloc_scalar,
        &bits_public,
        proof_alloc_scalars,
        statics,
        &tree.hash_params,
        x,
        y,
    )?;

    let proof = prover.prove(bp_gens)?;
    Ok((proof, (com_root, com_leaf, proof_comms), root_blinding))
}

pub fn verify_single_attribute_range_proof<T: BorrowMut<Transcript>>(
    tree_params: (usize, &Poseidon),
    idx: usize,
    x: u64,
    y: u64,
    commitments: &(
        CompressedRistretto,
        CompressedRistretto,
        Vec<CompressedRistretto>,
    ),
    proof: &R1CSProof,
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    mut verifier: Verifier<T>,
) -> Result<(), R1CSError> {
    if x >= y {
        return Err(R1CSError::GadgetError {
            description: format!(
                "Invalid range parameters: x={} must be less than y={}",
                x, y
            ),
        });
    }

    let depth = tree_params.0;
    let poseidon = tree_params.1;
    let k = Scalar::from(idx as u64);
    let bits_bool = get_bits(&k, depth);
    let bits_public: Vec<Scalar> = bits_bool
        .iter()
        .take(depth)
        .map(|b| Scalar::from(*b as u8))
        .collect();

    let var_root = verifier.commit(commitments.0);
    let root_alloc = AllocatedScalar {
        variable: var_root,
        assignment: None,
    };

    let var_leaf = verifier.commit(commitments.1);
    let leaf_alloc = AllocatedScalar {
        variable: var_leaf,
        assignment: None,
    };

    let mut proof_allocs = vec![];
    for c in &commitments.2 {
        let v = verifier.commit(*c);
        proof_allocs.push(AllocatedScalar {
            variable: v,
            assignment: None,
        });
    }

    let num_statics = 4;
    let statics =
        allocate_statics_for_verifier(&mut verifier, num_statics, pc_gens);

    attribute_tree_path_verify_with_range_gadget(
        &mut verifier,
        depth,
        root_alloc,
        leaf_alloc,
        &bits_public,
        proof_allocs,
        statics,
        &poseidon,
        x,
        y,
    )?;

    verifier.verify(proof, pc_gens, bp_gens)?;

    Ok(())
}
