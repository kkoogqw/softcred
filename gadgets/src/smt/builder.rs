use bulletproofs::BulletproofGens;
use curve25519_dalek::Scalar;

use crate::{poseidon::{builder::{Poseidon, PoseidonBuilder}, sbox::PoseidonSbox}, smt::{VanillaSparseMerkleTree, DEFAULT_TREE_DEPTH}};



pub struct SparseMerkleTreeBuilder {
	/// The depth of the tree
	pub depth: Option<usize>,
	/// The hash params, defaults to Poseidon
	/// TODO: Add abstract hasher
	hash_params: Option<Poseidon>,
	/// The merkle root of the tree
	pub root: Option<Scalar>,
}

impl SparseMerkleTreeBuilder {
	pub fn new() -> Self {
		Self {
			depth: None,
			hash_params: None,
			root: None,
		}
	}

	pub fn depth(mut self, depth: usize) -> Self {
		self.depth = Some(depth);
		self
	}

	pub fn hash_params(mut self, hash_params: Poseidon) -> Self {
		self.hash_params = Some(hash_params);
		self
	}

	pub fn root(mut self, root: Scalar) -> Self {
		self.root = Some(root);
		self
	}

	pub fn build(self) -> VanillaSparseMerkleTree {
		let depth = self.depth.unwrap_or(DEFAULT_TREE_DEPTH);
		let hash_params = self.hash_params.unwrap_or(
			PoseidonBuilder::new(6)
				.sbox(PoseidonSbox::Inverse)
				.bulletproof_gens(BulletproofGens::new(4096, 1))
				.build(),
		);
		VanillaSparseMerkleTree::new(hash_params, depth)
	}
}