use bulletproofs::r1cs::R1CSError;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable};
use curve25519_dalek::scalar::Scalar;

/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn positive_no_gadget<CS: ConstraintSystem>(
	cs: &mut CS,
	v: Variable,
	vs: Option<u64>,
	bit_size: usize,
) -> Result<(), R1CSError> {
	let mut constraint_v = vec![(v, -Scalar::one())];
	let mut exp_2 = Scalar::one();
	for i in 0..bit_size {
		// Create low-level variables and add them to constraints

		let (a, b, o) = cs.allocate_multiplier(vs.map(|q| {
			let bit: u64 = (q >> i) & 1;
			((1 - bit).into(), bit.into())
		}))?;

		// Enforce a * b = 0, so one of (a,b) is zero
		cs.constrain(o.into());

		// Enforce that a = 1 - b, so they both are 1 or 0.
		cs.constrain(a + (b - 1u64));

		constraint_v.push((b, exp_2));
		exp_2 = exp_2 + exp_2;
	}

	// Enforce that -v + Sum(b_i * 2^i, i = 0..n-1) = 0 => Sum(b_i * 2^i, i = 0..n-1) = v
	cs.constrain(constraint_v.iter().collect());

	Ok(())
}

pub fn bound_check_gadget<CS: ConstraintSystem>(
	cs: &mut CS,
	_v: Variable,
	a: Variable,
	b: Variable,
	a_s: Option<u64>,
	b_s: Option<u64>,
	max: u64,
	min: u64,
	n: usize,
) -> Result<(), R1CSError> {
	// a + b = max - min
	let lc_max_minus_min: LinearCombination = vec![(Variable::One(), Scalar::from(max - min))]
		.iter()
		.collect();

	// Constrain a + b to be same as max - min.
	cs.constrain(a + b - lc_max_minus_min);

	// Constrain a in [0, 2^n)
	assert!(positive_no_gadget(cs, a, a_s, n).is_ok());
	// Constrain b in [0, 2^n)
	assert!(positive_no_gadget(cs, b, b_s, n).is_ok());

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::bound_check_gadget;
	use bulletproofs::r1cs::{Prover, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use curve25519_dalek::scalar::Scalar;
	use merlin::Transcript;

	#[test]
	fn test_bound_check_gadget() {
		use rand::{thread_rng, Rng};

		let mut rng = thread_rng();
		let min = 10;
		let max = 100;

		let v = rng.gen_range(min, max);
		println!("v is {}", &v);
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		// TODO: Use correct bit size of the field
		let n = 32;

		let a = v - min;
		let b = max - v;

		// Prover makes a `ConstraintSystem` instance representing a range proof gadget
		let mut prover_transcript = Transcript::new(b"BoundsTest");
		let mut rng = rand::thread_rng();
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let (com_v, var_v) = prover.commit(v.into(), Scalar::random(&mut rng));
		let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
		let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));

		assert!(bound_check_gadget(
			&mut prover,
			var_v,
			var_a,
			var_b,
			Some(a),
			Some(b),
			max,
			min,
			n
		)
		.is_ok());

		let proof = prover.prove(&bp_gens);
		assert!(proof.is_ok());
		let proof = proof.unwrap();

		let mut verifier_transcript = Transcript::new(b"BoundsTest");
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let var_v = verifier.commit(com_v);
		let var_a = verifier.commit(com_a);
		let var_b = verifier.commit(com_b);

		assert!(
			bound_check_gadget(&mut verifier, var_v, var_a, var_a, None, None, max, min, n).is_ok()
		);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
