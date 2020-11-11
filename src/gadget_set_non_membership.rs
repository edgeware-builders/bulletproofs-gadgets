use crate::gadget_not_equals::is_nonzero_gadget;
use bulletproofs::r1cs::LinearCombination;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

pub fn set_non_membership_gadget<CS: ConstraintSystem>(
	cs: &mut CS,
	v: Variable,
	diff_vars: Vec<Variable>,
	diff_inv_vars: Vec<Variable>,
	set: &[u64],
) -> Result<(), R1CSError> {
	let set_length = set.len();

	for i in 0..set_length {
		// Take difference of value and each set element, `v - set[i]`
		let elem_lc: LinearCombination = vec![(Variable::One(), Scalar::from(set[i]))]
			.iter()
			.collect();
		let v_minus_elem = v - elem_lc;

		// Since `diff_vars[i]` is `set[i] - v`, `v - set[i]` + `diff_vars[i]` should be 0
		cs.constrain(diff_vars[i] + v_minus_elem);

		// Ensure `set[i] - v` is non-zero
		is_nonzero_gadget(cs, diff_vars[i], diff_inv_vars[i])?;
	}

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;
	use bulletproofs::r1cs::{Prover, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use curve25519_dalek::ristretto::CompressedRistretto;
	use merlin::Transcript;

	#[test]
	// Prove that difference between each set element and value is non-zero, hence value does not equal any set element.
	fn set_non_membership_check_gadget() {
		let set: Vec<u64> = vec![2, 3, 5, 6, 8, 20, 25];
		let value = 10u64;

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let set_length = set.len();

		let (proof, commitments) = {
			let mut comms: Vec<CompressedRistretto> = vec![];
			let mut diff_vars: Vec<Variable> = vec![];
			let mut diff_inv_vars: Vec<Variable> = vec![];

			let mut prover_transcript = Transcript::new(b"SetNonMemebershipTest");
			let mut rng = rand::thread_rng();

			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
			let value = Scalar::from(value);
			let (com_value, var_value) = prover.commit(value.clone(), Scalar::random(&mut rng));
			comms.push(com_value);

			for i in 0..set_length {
				let elem = Scalar::from(set[i]);
				let diff = elem - value;
				let diff_inv = diff.invert();

				// Take difference of set element and value, `set[i] - value`
				let (com_diff, var_diff) = prover.commit(diff.clone(), Scalar::random(&mut rng));
				diff_vars.push(var_diff);
				comms.push(com_diff);

				// Inverse needed to prove that difference `set[i] - value` is non-zero
				let (com_diff_inv, var_diff_inv) =
					prover.commit(diff_inv.clone(), Scalar::random(&mut rng));
				diff_inv_vars.push(var_diff_inv);
				comms.push(com_diff_inv);
			}

			assert!(set_non_membership_gadget(
				&mut prover,
				var_value,
				diff_vars,
				diff_inv_vars,
				&set
			)
			.is_ok());

			println!(
				"For set size {}, no of constraints is {}",
				&set_length,
				&prover.num_constraints()
			);

			let proof = prover.prove(&bp_gens);
			assert!(proof.is_ok());

			(proof.unwrap(), comms)
		};

		let mut verifier_transcript = Transcript::new(b"SetNonMemebershipTest");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let mut diff_vars: Vec<Variable> = vec![];
		let mut diff_inv_vars: Vec<Variable> = vec![];

		let var_val = verifier.commit(commitments[0]);

		for i in 1..set_length + 1 {
			let var_diff = verifier.commit(commitments[2 * i - 1]);
			diff_vars.push(var_diff);

			let var_diff_inv = verifier.commit(commitments[2 * i]);
			diff_inv_vars.push(var_diff_inv);
		}

		assert!(
			set_non_membership_gadget(&mut verifier, var_val, diff_vars, diff_inv_vars, &set)
				.is_ok()
		);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
