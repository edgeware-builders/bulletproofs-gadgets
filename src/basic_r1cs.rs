#[cfg(test)]
mod tests {
	use bulletproofs::r1cs::LinearCombination;
	use bulletproofs::r1cs::{ConstraintSystem, Prover, Variable, Verifier};
	use bulletproofs::{BulletproofGens, PedersenGens};
	use curve25519_dalek::scalar::Scalar;
	use merlin::Transcript;
	use rand::{thread_rng, Rng};

	#[test]
	fn test_zero() {
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let x = 0u64;

		let mut prover_transcript = Transcript::new(b"Zero");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let mut rng = thread_rng();
		let (com_x, var_x) = prover.commit(x.into(), Scalar::random(&mut rng));
		let (_, _, res) = prover.multiply(var_x.into(), var_x.into());
		prover.constrain(res.into());

		let proof = prover.prove(&bp_gens).unwrap();

		// Verifier
		let mut verifier_transcript = Transcript::new(b"Zero");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_x = verifier.commit(com_x);

		let (_, _, ver_res) = verifier.multiply(var_x.into(), var_x.into());
		verifier.constrain(ver_res.into());

		let res = verifier.verify(&proof, &pc_gens, &bp_gens);
		println!("{:?}", res);
		assert!(res.is_ok());
	}

	#[test]
	// One of the values is 0
	fn test_one_of_zero() {
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let (a, b, c, d) = (0u64, 5u64, 7u64, 8u64);

		let mut prover_transcript = Transcript::new(b"OneOfIsZero");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let mut rng = thread_rng();
		let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
		let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
		let (com_c, var_c) = prover.commit(c.into(), Scalar::random(&mut rng));
		let (com_d, var_d) = prover.commit(d.into(), Scalar::random(&mut rng));
		// a * b * c * d = 0 * 5 * 7 * 8 = 0
		let (_, _, res1) = prover.multiply(var_a.into(), var_b.into());
		let (_, _, res2) = prover.multiply(var_c.into(), var_d.into());
		let (_, _, res3) = prover.multiply(res1.into(), res2.into());
		prover.constrain(res3.into());

		let proof = prover.prove(&bp_gens).unwrap();

		// Verifier
		let mut verifier_transcript = Transcript::new(b"OneOfIsZero");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_a = verifier.commit(com_a);
		let var_b = verifier.commit(com_b);
		let var_c = verifier.commit(com_c);
		let var_d = verifier.commit(com_d);

		let (_, _, ver_res1) = verifier.multiply(var_a.into(), var_b.into());
		let (_, _, ver_res2) = verifier.multiply(var_c.into(), var_d.into());
		let (_, _, ver_res3) = verifier.multiply(ver_res1.into(), ver_res2.into());
		verifier.constrain(ver_res3.into());

		let res = verifier.verify(&proof, &pc_gens, &bp_gens);
		println!("{:?}", res);
		assert!(res.is_ok());
	}

	#[test]
	// should have zero and one only
	fn test_zero_and_one() {
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let (a, b) = (0u64, 1u64);

		let mut prover_transcript = Transcript::new(b"ZeroAndOne");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let mut rng = thread_rng();
		let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
		let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));

		let (_, _, res1) = prover.multiply(var_a.into(), var_b.into());
		prover.constrain(res1.into());
		prover.constrain(var_a + (var_b - 1u64));

		let proof = prover.prove(&bp_gens).unwrap();

		let mut verifier_transcript = Transcript::new(b"ZeroAndOne");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_a = verifier.commit(com_a);
		let var_b = verifier.commit(com_b);

		let (_, _, ver_res1) = verifier.multiply(var_a.into(), var_b.into());
		verifier.constrain(ver_res1.into());
		verifier.constrain(var_a + (var_b - 1u64));
		let res = verifier.verify(&proof, &pc_gens, &bp_gens);
		println!("{:?}", res);
		assert!(res.is_ok());
	}

	#[test]
	fn test_poly_equal() {
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let mut prover_transcript = Transcript::new(b"PolyEqual");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let (a, b, c, d) = (14u64, 13u64, 14u64, 13u64);

		let mut rng = thread_rng();
		let x = Scalar::random(&mut rng);

		let (com_a, var_a) = prover.commit(a.into(), Scalar::random(&mut rng));
		let (com_b, var_b) = prover.commit(b.into(), Scalar::random(&mut rng));
		let (com_c, var_c) = prover.commit(c.into(), Scalar::random(&mut rng));
		let (com_d, var_d) = prover.commit(d.into(), Scalar::random(&mut rng));

		let (_, _, input_mul) = prover.multiply(var_a - x, var_b - x);
		let (_, _, output_mul) = prover.multiply(var_c - x, var_d - x);

		prover.constrain(input_mul - output_mul);

		let proof = prover.prove(&bp_gens).unwrap();

		let mut verifier_transcript = Transcript::new(b"PolyEqual");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_a = verifier.commit(com_a);
		let var_b = verifier.commit(com_b);
		let var_c = verifier.commit(com_c);
		let var_d = verifier.commit(com_d);

		let (_, _, input_mul) = verifier.multiply(var_a - x, var_b - x);
		let (_, _, output_mul) = verifier.multiply(var_c - x, var_d - x);
		println!("{:?}", input_mul - output_mul);
		verifier.constrain(input_mul - output_mul);

		let res = verifier.verify(&proof, &pc_gens, &bp_gens);
		println!("{:?}", res);
		assert!(res.is_ok());
	}

	#[test]
	fn test_factor_r1cs() {
		// Prove knowledge of `p` and `q` such that given an `r`, `p * q = r`

		// TODO: Prove that neither `p` or `q` is 1, this can be done range proof gadget or using the `not_equals_gadget`
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let (p, q, r) = (17u64, 19u64, 323u64);

		let mut prover_transcript = Transcript::new(b"Factors");
		let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

		let mut rng = thread_rng();

		let (com_p, var_p) = prover.commit(p.into(), Scalar::random(&mut rng));
		let (com_q, var_q) = prover.commit(q.into(), Scalar::random(&mut rng));

		let (_, _, o) = prover.multiply(var_p.into(), var_q.into());
		let lc: LinearCombination = vec![(Variable::One(), r.into())].iter().collect();
		prover.constrain(o - lc);

		let proof = prover.prove(&bp_gens).unwrap();

		let mut verifier_transcript = Transcript::new(b"Factors");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_p = verifier.commit(com_p);
		let var_q = verifier.commit(com_q);

		let (_, _, o) = verifier.multiply(var_p.into(), var_q.into());
		let lc: LinearCombination = vec![(Variable::One(), r.into())].iter().collect();
		verifier.constrain(o - lc);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}

	#[test]
	fn test_factor_r1cs_2() {
		// Prove knowledge of `p`, `q` and `r` such that given an `s`, `p * q * r = s`

		// TODO: Prove that neither `p` or `q` or `r` is 1, this can be done range proof gadget.
		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(128, 1);

		let (p, q, r, s) = (5u64, 7u64, 3u64, 105u64);

		let (proof, commitments) = {
			let mut prover_transcript = Transcript::new(b"Factors");
			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

			let mut rng = thread_rng();

			let (com_p, var_p) = prover.commit(p.into(), Scalar::random(&mut rng));
			let (com_q, var_q) = prover.commit(q.into(), Scalar::random(&mut rng));
			let (com_r, var_r) = prover.commit(r.into(), Scalar::random(&mut rng));

			let (_, _, o1) = prover.multiply(var_p.into(), var_q.into());
			let (_, _, o2) = prover.multiply(o1.into(), var_r.into());
			let lc: LinearCombination = vec![(Variable::One(), s.into())].iter().collect();
			prover.constrain(o2 - lc);

			let proof = prover.prove(&bp_gens).unwrap();

			(proof, (com_p, com_q, com_r))
		};

		let mut verifier_transcript = Transcript::new(b"Factors");
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let var_p = verifier.commit(commitments.0);
		let var_q = verifier.commit(commitments.1);
		let var_r = verifier.commit(commitments.2);

		let (_, _, o1) = verifier.multiply(var_p.into(), var_q.into());
		let (_, _, o2) = verifier.multiply(o1.into(), var_r.into());
		let lc: LinearCombination = vec![(Variable::One(), s.into())].iter().collect();
		verifier.constrain(o2 - lc);

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}
}
