use crate::scalar_utils::TREE_DEPTH;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

use crate::gadget_poseidon::{
	PoseidonParams, Poseidon_hash_2, Poseidon_hash_2_constraints, SboxType,
};

type DBVal = (Scalar, Scalar);

pub struct MerkleTree {
	pub leaf_count: u32,
	pub max_leaves: u32,
	pub root_hash: Scalar,
	pub edge_nodes: Vec<Scalar>,
	pub hash_constants: PoseidonParams,
}

impl MerkleTree {
	pub fn new(hash_constants: PoseidonParams) -> Self {
		let depth = TREE_DEPTH;
		Self {
			root_hash: Scalar::zero(),
			leaf_count: 0,
			max_leaves: u32::MAX >> (32 - depth),
			edge_nodes: vec![Scalar::zero(); depth as usize],
			hash_constants,
		}
	}

	pub fn insert(&mut self, val: Scalar) -> Scalar {
		let mut edge_index = self.leaf_count;
		let mut pair_hash = val;
		// Update the tree
		for i in 0..self.edge_nodes.len() {
			if edge_index % 2 == 0 {
				self.edge_nodes[i] = pair_hash;
			}

			let hash = self.edge_nodes[i];
			pair_hash = Poseidon_hash_2(hash, pair_hash, &self.hash_constants, &SboxType::Inverse);

			edge_index /= 2;
		}

		self.leaf_count += 1;
		self.root_hash = pair_hash;
		pair_hash
	}

	pub fn verify_proof(&self, pub_key: Scalar, path: Vec<(bool, Scalar)>) -> bool {
		let mut hash = pub_key;
		for (is_right, node) in path {
			hash = match is_right {
				true => Poseidon_hash_2(hash, node, &self.hash_constants, &SboxType::Inverse),
				false => Poseidon_hash_2(node, hash, &self.hash_constants, &SboxType::Inverse),
			}
		}
		hash == self.root_hash
	}
}

/// left = (1-leaf_side) * leaf + (leaf_side * proof_node)
/// right = leaf_side * leaf + ((1-leaf_side) * proof_node))
pub fn merkle_tree_verif_gadget<CS: ConstraintSystem>(
	cs: &mut CS,
	depth: usize,
	root: &Scalar,
	leaf_val: Variable,
	leaf_index_bits: Vec<Variable>,
	proof_nodes: Vec<Variable>,
	statics: Vec<Variable>,
	poseidon_params: &PoseidonParams,
) -> Result<(), R1CSError> {
	let mut prev_hash = LinearCombination::from(leaf_val);

	let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();

	for i in 0..depth {
		let leaf_val_lc = prev_hash.clone();
		let one_minus_leaf_side: LinearCombination = Variable::One() - leaf_index_bits[i];

		let (_, _, left_1) = cs.multiply(one_minus_leaf_side.clone(), leaf_val_lc.clone());
		let (_, _, left_2) = cs.multiply(leaf_index_bits[i].into(), proof_nodes[i].into());
		let left = left_1 + left_2;

		let (_, _, right_1) = cs.multiply(leaf_index_bits[i].into(), leaf_val_lc);
		let (_, _, right_2) = cs.multiply(one_minus_leaf_side, proof_nodes[i].into());
		let right = right_1 + right_2;

		// prev_hash = mimc_hash_2::<CS>(cs, left, right, mimc_rounds, mimc_constants)?;
		prev_hash = Poseidon_hash_2_constraints::<CS>(
			cs,
			left,
			right,
			statics.clone(),
			poseidon_params,
			&SboxType::Inverse,
		)?;
	}

	cs.constrain(prev_hash - *root);

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::gadget_poseidon::{
		allocate_statics_for_prover, allocate_statics_for_verifier, Poseidon_hash_2_gadget,
	};
	use bulletproofs::r1cs::{Prover, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use merlin::Transcript;
	use rand::rngs::StdRng;
	use rand::SeedableRng;

	fn get_poseidon_params() -> PoseidonParams {
		let width = 6;
		let (full_b, full_e) = (4, 4);
		let partial_rounds = 140;
		PoseidonParams::new(width, full_b, full_e, partial_rounds)
	}

	#[test]
	fn test_pair_hash() {
		let sbox_type = &SboxType::Cube;
		let s_params = get_poseidon_params();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let xl = Scalar::random(&mut test_rng);
		let xr = Scalar::random(&mut test_rng);
		let expected_output = Poseidon_hash_2(xl, xr, &s_params, sbox_type);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		let mut prover_transcript = Transcript::new(b"pair_hash");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let (com_l, var_l) = prover.commit(xl.clone(), Scalar::random(&mut test_rng));
		let (com_r, var_r) = prover.commit(xr.clone(), Scalar::random(&mut test_rng));

		let num_statics = 4;
		let statics = allocate_statics_for_prover(&mut prover, num_statics);

		let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
		let hash = Poseidon_hash_2_constraints(
			&mut prover,
			var_l.into(),
			var_r.into(),
			statics,
			&s_params,
			sbox_type,
		)
		.unwrap();

		prover.constrain(hash - expected_output);

		let proof = prover.prove(&bp_gens).unwrap();

		let mut verifier_transcript = Transcript::new(b"pair_hash");
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let lv = verifier.commit(com_l);
		let rv = verifier.commit(com_r);

		let num_statics = 4;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
		let hash = Poseidon_hash_2_constraints(
			&mut verifier,
			lv.into(),
			rv.into(),
			statics,
			&s_params,
			sbox_type,
		)
		.unwrap();

		verifier.constrain(hash - expected_output);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
