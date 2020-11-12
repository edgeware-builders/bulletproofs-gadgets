use crate::scalar_utils::TREE_DEPTH;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

use crate::poseidon::Poseidon;
use crate::sbox::SboxType;

type DBVal = (Scalar, Scalar);

pub struct MerkleTree {
	pub leaf_count: u32,
	pub max_leaves: u32,
	pub root_hash: Scalar,
	pub edge_nodes: Vec<Scalar>,
	pub poseidon: Poseidon,
}

impl MerkleTree {
	pub fn new(poseidon: Poseidon) -> Self {
		let depth = TREE_DEPTH;
		Self {
			root_hash: Scalar::zero(),
			leaf_count: 0,
			max_leaves: u32::MAX >> (32 - depth),
			edge_nodes: vec![Scalar::zero(); depth as usize],
			poseidon,
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
			pair_hash = self.poseidon.hash_2(hash, pair_hash, &SboxType::Inverse);

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
				true => self.poseidon.hash_2(hash, node, &SboxType::Inverse),
				false => self.poseidon.hash_2(node, hash, &SboxType::Inverse),
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
	poseidon: &Poseidon,
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
		prev_hash = poseidon.hash_2_constraints::<CS>(
			cs,
			left,
			right,
			statics.clone(),
			&SboxType::Inverse,
		)?;
	}

	cs.constrain(prev_hash - *root);

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::gadget_poseidon::{allocate_statics_for_prover, allocate_statics_for_verifier};
	use crate::mimc::{mimc, mimc_constraints, MIMC_ROUNDS};
	use bulletproofs::r1cs::{LinearCombination, Prover, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use merlin::Transcript;
	use rand::rngs::StdRng;
	use rand::SeedableRng;
	use std::time::Instant;

	fn get_poseidon_params() -> Poseidon {
		let width = 6;
		let (full_b, full_e) = (4, 4);
		let partial_rounds = 140;
		Poseidon::new(width, full_b, full_e, partial_rounds)
	}

	#[test]
	fn test_pair_hash_mimc() {
		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let xl = Scalar::random(&mut test_rng);
		let xr = Scalar::random(&mut test_rng);
		let constants = (0..MIMC_ROUNDS)
			.map(|_| Scalar::random(&mut test_rng))
			.collect::<Vec<_>>();
		let out = mimc(&xl, &xr, &constants);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		let mut prover_transcript = Transcript::new(b"pair_hash");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let (com_l, var_l) = prover.commit(xl.clone(), Scalar::random(&mut test_rng));
		let (com_r, var_r) = prover.commit(xr.clone(), Scalar::random(&mut test_rng));
		let exp = mimc_constraints(&mut prover, &var_l.into(), &var_r.into(), &constants);

		prover.constrain(exp - out);
		let proof = prover.prove(&bp_gens).unwrap();

		let mut verifier_transcript = Transcript::new(b"pair_hash");
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let lv = verifier.commit(com_l);
		let rv = verifier.commit(com_r);

		let exp = mimc_constraints(&mut verifier, &lv.into(), &rv.into(), &constants);
		verifier.constrain(exp - out);
		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}

	#[test]
	fn test_simple_proof_path() {
		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let a = Scalar::random(&mut test_rng);
		let b = Scalar::random(&mut test_rng);
		let c = Scalar::random(&mut test_rng);
		let d = Scalar::random(&mut test_rng);
		let constants = (0..MIMC_ROUNDS)
			.map(|_| Scalar::random(&mut test_rng))
			.collect::<Vec<_>>();
		let out1 = mimc(&a, &b, &constants);
		let out2 = mimc(&c, &d, &constants);
		let root = mimc(&out1, &out2, &constants);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		let mut prover_transcript = Transcript::new(b"proof");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let (com_a, var_a) = prover.commit(a.clone(), Scalar::random(&mut test_rng));
		let (com_b, var_b) = prover.commit(b.clone(), Scalar::random(&mut test_rng));
		let (com_out2, var_out2) = prover.commit(out2.clone(), Scalar::random(&mut test_rng));

		let out1 = mimc_constraints(&mut prover, &var_a.into(), &var_b.into(), &constants);
		let root_con = mimc_constraints(&mut prover, &out1.into(), &var_out2.into(), &constants);

		prover.constrain(root_con - root);
		let proof = prover.prove(&bp_gens).unwrap();

		let mut verifier_transcript = Transcript::new(b"proof");
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let var_a = verifier.commit(com_a);
		let var_b = verifier.commit(com_b);
		let var_out2 = verifier.commit(com_out2);

		let out1 = mimc_constraints(&mut verifier, &var_a.into(), &var_b.into(), &constants);
		let root_ver = mimc_constraints(&mut verifier, &out1.into(), &var_out2.into(), &constants);
		verifier.constrain(root_ver - root);
		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}

	#[test]
	fn test_pair_hash_poseidon() {
		let sbox_type = &SboxType::Cube;
		let poseidon = get_poseidon_params();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let xl = Scalar::random(&mut test_rng);
		let xr = Scalar::random(&mut test_rng);
		let expected_output = poseidon.hash_2(xl, xr, sbox_type);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		let mut prover_transcript = Transcript::new(b"pair_hash");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let (com_l, var_l) = prover.commit(xl.clone(), Scalar::random(&mut test_rng));
		let (com_r, var_r) = prover.commit(xr.clone(), Scalar::random(&mut test_rng));

		let num_statics = 4;
		let statics = allocate_statics_for_prover(&mut prover, num_statics);

		let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
		let hash = poseidon
			.hash_2_constraints(&mut prover, var_l.into(), var_r.into(), statics, sbox_type)
			.unwrap();

		prover.constrain(hash - expected_output);

		let proof = prover.prove(&bp_gens).unwrap();

		let start = Instant::now();
		let mut verifier_transcript = Transcript::new(b"pair_hash");
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let lv = verifier.commit(com_l);
		let rv = verifier.commit(com_r);

		let num_statics = 4;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
		let hash = poseidon
			.hash_2_constraints(&mut verifier, lv.into(), rv.into(), statics, sbox_type)
			.unwrap();

		verifier.constrain(hash - expected_output);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
		let end = start.elapsed();

		println!("Verification time is {:?}", end);
		panic!("asd");
	}
}
