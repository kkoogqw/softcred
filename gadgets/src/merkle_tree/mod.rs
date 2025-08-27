use std::{sync::Arc, vec};

// A 16-leaf attribute tree from poseidon hash
use curve25519_dalek::Scalar;
use group::ff::Field;
use serde::{Deserialize, Serialize};

use crate::poseidon::{builder::Poseidon, Poseidon_hash_4};

/// A 4-ary attribute tree, support 16 attributes.
#[derive(Clone, Debug)]
pub struct MerkleTree16x4 {
    leaves: [Scalar; 16],
    level1_hashes: [Scalar; 4], 
    root: Scalar,
    params: Poseidon,
}

#[derive(Clone, Debug)]
pub struct MerkleTree16x4Path {
    pub leaf: Scalar,
    /// 0..3
    pub group_id: u8,
    /// 0..3
    pub pos_in_group: u8,
    /// nodes in current group（in the fixed order 0..3）
    pub children0: [Scalar; 4],
    /// hashs of groups（in the fixed order 0..3）
    pub children1: [Scalar; 4],
    /// root of tree
    pub root: Scalar,
}

impl MerkleTree16x4 {
    pub fn new(params: Poseidon) -> Self {
        let leaves = [Scalar::ZERO; 16];
        let mt = Self {
            leaves,
            level1_hashes: [Scalar::ZERO; 4],
            root: Scalar::ZERO,
            params,
        };
        // mt.recompute_root();
        mt
    }

    pub fn set_leaf(&mut self, i: usize, val: Scalar) {
        assert!(i < 16);
        self.leaves[i] = val;
        self.recompute_root();
    }

    pub fn build(&mut self, vals: Vec<Scalar>) {
        assert!(vals.len() == 16);
        self.leaves.copy_from_slice(vals.as_slice());
        self.recompute_root();
    }

    pub fn get_root(&self) -> Scalar {
        self.root
    }

    fn recompute_root(&mut self) {
        // for group 0..3, each group with 4 leaves.
        for g in 0..4 {
            let base = g * 4;
            self.level1_hashes[g] = Poseidon_hash_4(
                [
                    self.leaves[base + 0],
                    self.leaves[base + 1],
                    self.leaves[base + 2],
                    self.leaves[base + 3],
                ],
                &self.params,
            );
        }
        self.root = Poseidon_hash_4(self.level1_hashes, &self.params);
    }

    /// build the path to the i-th attribute
    pub fn path_prove(&self, i: usize) -> MerkleTree16x4Path {
        assert!(i < 16);
        let group_id = i / 4;        // 0..3
        let pos_in_group = i % 4;    // 0..3
        let base = group_id * 4;

        let children0 = [
            self.leaves[base + 0],
            self.leaves[base + 1],
            self.leaves[base + 2],
            self.leaves[base + 3],
        ];

        let children1 = self.level1_hashes;

        MerkleTree16x4Path {
            leaf: self.leaves[i],
            group_id: group_id as u8,
            pos_in_group: pos_in_group as u8,
            children0,
            children1,
            root: self.root,
        }
    }

    /// Verify the path with root.
    pub fn path_verify(&self, root: Scalar, proof: &MerkleTree16x4Path) -> bool {
        if proof.root != root {
            return false;
        }
        if proof.group_id as usize > 3 || proof.pos_in_group as usize > 3 {
            return false;
        }
        let pos = proof.pos_in_group as usize;
        let gid = proof.group_id as usize;

        // the position of leaf
        if proof.children0[pos] != proof.leaf {
            return false;
        }
        // the hash of group
        let h0 = Poseidon_hash_4(proof.children0, &self.params);
        if proof.children1[gid] != h0 {
            return false;
        }
        // the root should be consistent
        let root = Poseidon_hash_4(proof.children1, &self.params);
        root == proof.root
    }
}