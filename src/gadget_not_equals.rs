use bulletproofs::r1cs::LinearCombination;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

/// Enforces that x is not 0.
pub fn is_nonzero_gadget<CS: ConstraintSystem>(
	cs: &mut CS,
	x: Variable,
	x_inv: Variable,
) -> Result<(), R1CSError> {
	let y: u32 = 1;

	let x_lc: LinearCombination = vec![(x, Scalar::one())].iter().collect();
	let one_minus_y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(1 - y))]
		.iter()
		.collect();
	let y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(y))].iter().collect();

	// x * (1-y) = 0
	let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
	cs.constrain(o1.into());

	// x * x_inv = y
	let inv_lc: LinearCombination = vec![(x_inv, Scalar::one())].iter().collect();
	let (_, _, o2) = cs.multiply(x_lc.clone(), inv_lc.clone());
	// Output wire should have value `y`
	cs.constrain(o2 - y_lc);
	Ok(())
}

// Ensure `v` is not equal to expected
pub fn not_equals_gadget<CS: ConstraintSystem>(
	cs: &mut CS,
	v: Variable,
	diff_var: Variable,
	diff_inv_var: Variable,
	expected: &u64,
) -> Result<(), R1CSError> {
	let expected_lc: LinearCombination = vec![(Variable::One(), Scalar::from(*expected))]
		.iter()
		.collect();
	let v_minus_expected_lc = v - expected_lc;

	// ex - v = diff_var
	// diff_var - ex + v = 0
	// Since `diff_var` is `expected - v`, `v - expected` + `diff_var` should be 0
	// eg1:
	// ex: 5, v: 4, diff: 3
	// v - ex + diff = 4 - 5 + 3 = -1 + 3 = 2
	// eg2:
	// ex: 3, v: 5, diff: -2
	// v - ex + diff = 5 - 3 - 2 = 0
	cs.constrain(diff_var + v_minus_expected_lc);

	// Ensure `set[i] - v` is non-zero
	is_nonzero_gadget(cs, diff_var, diff_inv_var)?;

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::not_equals_gadget;
	use bulletproofs::r1cs::{Prover, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use curve25519_dalek::scalar::Scalar;
	use merlin::Transcript;

	#[test]
	// Prove that difference between value and expected is non-zero, hence val does not equal the expected.
	fn test_not_equals_gadget() {
		// Check that committed value is not equal to a public value
		let value = 10u64;
		let expected = 5u64;

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let mut prover_transcript = Transcript::new(b"NotEqualsTest");
		let mut rng = rand::thread_rng();
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let value = Scalar::from(value);
		let (com_value, var_value) = prover.commit(value.clone(), Scalar::random(&mut rng));

		let diff = Scalar::from(expected) - value;
		let (com_diff, var_diff) = prover.commit(diff.clone(), Scalar::random(&mut rng));

		let diff_inv = diff.invert();
		let (com_diff_inv, var_diff_inv) =
			prover.commit(diff_inv.clone(), Scalar::random(&mut rng));

		assert!(
			not_equals_gadget(&mut prover, var_value, var_diff, var_diff_inv, &expected).is_ok()
		);

		let res = prover.prove(&bp_gens);
		assert!(res.is_ok());
		let proof = res.unwrap();

		let mut verifier_transcript = Transcript::new(b"NotEqualsTest");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_val = verifier.commit(com_value);
		let var_diff = verifier.commit(com_diff);
		let var_diff_inv = verifier.commit(com_diff_inv);

		assert!(
			not_equals_gadget(&mut verifier, var_val, var_diff, var_diff_inv, &expected).is_ok()
		);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
