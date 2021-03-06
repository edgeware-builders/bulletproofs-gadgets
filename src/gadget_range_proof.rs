#[cfg(test)]
mod tests {
	use crate::gadget_bound_check::positive_no_gadget;
	use bulletproofs::r1cs::LinearCombination;
	use bulletproofs::r1cs::{ConstraintSystem, Prover, Variable, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use curve25519_dalek::scalar::Scalar;
	use merlin::Transcript;

	#[test]
	fn test_range_proof_gadget() {
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
		println!("a, b are {} {}", &a, &b);

		// Prover makes a `ConstraintSystem` instance representing a range proof gadget
		let mut prover_transcript = Transcript::new(b"BoundsTest");
		let mut rng = rand::thread_rng();

		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		// Constrain a in [0, 2^n)
		let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
		assert!(positive_no_gadget(&mut prover, var_a, Some(a), n).is_ok());

		// Constrain b in [0, 2^n)
		let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
		assert!(positive_no_gadget(&mut prover, var_b, Some(b), n).is_ok());

		// Constrain a+b to be same as max-min. This ensures same v is used in both commitments (`com_a` and `com_b`)
		let var_c: LinearCombination = vec![(Variable::One(), (max - min).into())].iter().collect();
		prover.constrain(var_a + var_b - var_c);

		let proof = prover.prove(&bp_gens);
		assert!(proof.is_ok());
		let proof = proof.unwrap();

		// Verifier makes a `ConstraintSystem` instance representing a merge gadget
		let mut verifier_transcript = Transcript::new(b"BoundsTest");
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let var_a = verifier.commit(com_a);
		assert!(positive_no_gadget(&mut verifier, var_a, None, n).is_ok());

		let var_b = verifier.commit(com_b);
		assert!(positive_no_gadget(&mut verifier, var_b, None, n).is_ok());

		//        println!("Verifier commitments {:?}", &commitments);

		let var_c: LinearCombination = vec![(Variable::One(), (max - min).into())].iter().collect();
		verifier.constrain(var_a + var_b - var_c);

		// Verifier verifies proof
		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
