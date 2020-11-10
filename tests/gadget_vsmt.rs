use bulletproofs::mimc::{mimc, MIMC_ROUNDS};
use bulletproofs::r1cs::{
	ConstraintSystem, LinearCombination, Prover, R1CSError, Variable, Verifier,
};
use bulletproofs::r1cs_utils::{constrain_lc_with_scalar, AllocatedScalar};
use bulletproofs::scalar_utils::{get_bits, get_bits_at, ScalarBits, ScalarBytes, TREE_DEPTH};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;
use std::collections::HashMap;

use bulletproofs::poseidon::{
	allocate_statics_for_prover, allocate_statics_for_verifier, PoseidonParams, Poseidon_hash_2,
	Poseidon_hash_2_constraints, SboxType,
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
	leaf_val: AllocatedScalar,
	leaf_index_bits: Vec<AllocatedScalar>,
	proof_nodes: Vec<AllocatedScalar>,
	statics: Vec<AllocatedScalar>,
	poseidon_params: &PoseidonParams,
) -> Result<(), R1CSError> {
	let mut prev_hash = LinearCombination::default();

	let statics: Vec<LinearCombination> = statics.iter().map(|s| s.variable.into()).collect();

	for i in 0..depth {
		let leaf_val_lc = if i == 0 {
			LinearCombination::from(leaf_val.variable)
		} else {
			prev_hash.clone()
		};
		let one_minus_leaf_side: LinearCombination = Variable::One() - leaf_index_bits[i].variable;

		let (_, _, left_1) = cs.multiply(one_minus_leaf_side.clone(), leaf_val_lc.clone());
		let (_, _, left_2) = cs.multiply(
			leaf_index_bits[i].variable.into(),
			proof_nodes[i].variable.into(),
		);
		let left = left_1 + left_2;

		let (_, _, right_1) = cs.multiply(leaf_index_bits[i].variable.into(), leaf_val_lc);
		let (_, _, right_2) = cs.multiply(one_minus_leaf_side, proof_nodes[i].variable.into());
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

	constrain_lc_with_scalar::<CS>(cs, prev_hash, root);

	Ok(())
}

pub fn mul2(scalar: &Scalar) -> Scalar {
	scalar * Scalar::from(2u8)
}

pub fn div2(scalar: &Scalar) -> Scalar {
	let inv_2 = Scalar::from_canonical_bytes([
		247, 233, 122, 46, 141, 49, 9, 44, 107, 206, 123, 81, 239, 124, 111, 10, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 8,
	])
	.unwrap();
	scalar * inv_2
}

#[cfg(test)]
mod tests {
	use super::*;
	use curve25519_dalek::constants::BASEPOINT_ORDER;

	#[test]
	fn test_mul2_div2() {
		let x = Scalar::from(6 as u32);
		assert_eq!(Scalar::from(3 as u32), div2(&x));
		assert_eq!(Scalar::from(12 as u32), mul2(&x));
		let mut csprng = thread_rng();

		for _ in 0..100 {
			let r: Scalar = Scalar::random(&mut csprng);
			let r2 = mul2(&r);
			assert_eq!(r, div2(&r2));
		}
	}

	fn test_VSMT_Verif() {
		let mut test_rng = thread_rng();

		let width = 6;
		let (full_b, full_e) = (4, 4);
		let partial_rounds = 140;
		let total_rounds = full_b + partial_rounds + full_e;
		let p_params = PoseidonParams::new(width, full_b, full_e, partial_rounds);
		let mut tree = MerkleTree::new(p_params.clone());

		for i in 1..=10 {
			let s = Scalar::from(i as u32);
			tree.insert(s);
		}

		let mut merkle_proof_vec = Vec::<Scalar>::new();
		let mut merkle_proof = Some(merkle_proof_vec);
		let k = Scalar::from(7u32);
		// assert_eq!(k, tree.get(k, &mut merkle_proof));
		merkle_proof_vec = merkle_proof.unwrap();
		// assert!(tree.verify_proof(k, k, &merkle_proof_vec, None));
		// assert!(tree.verify_proof(k, k, &merkle_proof_vec, Some(&tree.root_hash)));

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(819200, 1);

		let (proof, commitments) = {
			let mut prover_transcript = Transcript::new(b"VSMT");
			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

			let (com_leaf, var_leaf) = prover.commit(k, Scalar::random(&mut test_rng));
			let leaf_alloc_scalar = AllocatedScalar {
				variable: var_leaf,
				assignment: Some(k),
			};

			let mut leaf_index_comms = vec![];
			let mut leaf_index_vars = vec![];
			let mut leaf_index_alloc_scalars = vec![];
			for b in get_bits_at(&k, TREE_DEPTH).iter() {
				let val: Scalar = Scalar::from(*b as u8);
				let (c, v) = prover.commit(val.clone(), Scalar::random(&mut test_rng));
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
			for p in merkle_proof_vec.iter().rev() {
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

			assert!(merkle_tree_verif_gadget(
				&mut prover,
				tree.edge_nodes.len(),
				&tree.root_hash,
				leaf_alloc_scalar,
				leaf_index_alloc_scalars,
				proof_alloc_scalars,
				statics,
				&p_params
			)
			.is_ok());

			let proof = prover.prove(&bp_gens).unwrap();

			(proof, (com_leaf, leaf_index_comms, proof_comms))
		};

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
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		assert!(merkle_tree_verif_gadget(
			&mut verifier,
			tree.edge_nodes.len(),
			&tree.root_hash,
			leaf_alloc_scalar,
			leaf_index_alloc_scalars,
			proof_alloc_scalars,
			statics,
			&p_params
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
