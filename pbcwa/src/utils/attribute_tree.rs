use curve25519_dalek::Scalar;
use gadgets::{merkle_tree::{MerkleTree16x4, MerkleTree16x4Path}, smt::{builder::SparseMerkleTreeBuilder, VanillaSparseMerkleTree}};


pub type Attribute = Scalar;
// pub type AttributeTree = MerkleTree16x4;
// pub type AttributePath = MerkleTree16x4Path;
pub type AttributeTree = VanillaSparseMerkleTree;
pub type AttributeTreeBuilder = SparseMerkleTreeBuilder;
pub type Root = Scalar;
