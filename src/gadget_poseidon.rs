#![allow(non_snake_case)]
use crate::poseidon::{Poseidon, PADDING_CONST, ZERO_CONST};
use crate::sbox::SboxType;
use bulletproofs::r1cs::{
	ConstraintSystem, LinearCombination, Prover, R1CSError, Variable, Verifier,
};
use bulletproofs::PedersenGens;
use curve25519_dalek::scalar::Scalar;

pub fn Poseidon_permutation_gadget<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	input: Vec<Variable>,
	poseidon: &'a Poseidon,
	sbox_type: &SboxType,
	output: &[Scalar],
) -> Result<(), R1CSError> {
	let width = poseidon.width;
	assert_eq!(output.len(), width);

	let input_vars: Vec<LinearCombination> = input.iter().map(|&e| e.into()).collect();
	let permutation_output = poseidon.permute_constraints::<CS>(cs, input_vars, sbox_type)?;

	for i in 0..width {
		cs.constrain(permutation_output[i].to_owned() - output[i]);
	}

	Ok(())
}

pub fn Poseidon_hash_2_gadget<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	xl: Variable,
	xr: Variable,
	statics: Vec<Variable>,
	poseidon: &'a Poseidon,
	sbox_type: &SboxType,
	output: &Scalar,
) -> Result<(), R1CSError> {
	let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
	let hash = poseidon.hash_2_constraints::<CS>(cs, xl.into(), xr.into(), statics, sbox_type)?;

	cs.constrain(hash - *output);

	Ok(())
}

pub fn Poseidon_hash_4_gadget<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	input: Vec<Variable>,
	statics: Vec<Variable>,
	poseidon: &'a Poseidon,
	sbox_type: &SboxType,
	output: &Scalar,
) -> Result<(), R1CSError> {
	let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
	let mut input_arr: [LinearCombination; 4] = [
		LinearCombination::default(),
		LinearCombination::default(),
		LinearCombination::default(),
		LinearCombination::default(),
	];
	for i in 0..input.len() {
		input_arr[i] = input[i].into();
	}
	let hash = poseidon.hash_4_constraints::<CS>(cs, input_arr, statics, sbox_type)?;

	cs.constrain(hash - *output);

	Ok(())
}

/// Allocate padding constant and zeroes for Prover
pub fn allocate_statics_for_prover(prover: &mut Prover, num_statics: usize) -> Vec<Variable> {
	let mut statics = vec![];
	let (_, var) = prover.commit(Scalar::from(ZERO_CONST), Scalar::zero());
	statics.push(var);

	// Commitment to PADDING_CONST with blinding as 0
	let (_, var) = prover.commit(Scalar::from(PADDING_CONST), Scalar::zero());
	statics.push(var);

	// Commit to 0 with randomness 0 for the rest of the elements of width
	for _ in 2..num_statics {
		let (_, var) = prover.commit(Scalar::from(ZERO_CONST), Scalar::zero());
		statics.push(var);
	}
	statics
}

/// Allocate padding constant and zeroes for Verifier
pub fn allocate_statics_for_verifier(
	verifier: &mut Verifier,
	num_statics: usize,
	pc_gens: &PedersenGens,
) -> Vec<Variable> {
	let mut statics = vec![];
	// Commitment to PADDING_CONST with blinding as 0
	let pad_comm = pc_gens
		.commit(Scalar::from(PADDING_CONST), Scalar::zero())
		.compress();

	// Commitment to 0 with blinding as 0
	let zero_comm = pc_gens
		.commit(Scalar::from(ZERO_CONST), Scalar::zero())
		.compress();

	let v = verifier.commit(zero_comm.clone());
	statics.push(v);

	let v = verifier.commit(pad_comm);
	statics.push(v);
	for _ in 2..num_statics {
		let v = verifier.commit(zero_comm.clone());
		statics.push(v);
	}
	statics
}

#[cfg(test)]
mod tests {
	use super::*;
	use bulletproofs::r1cs::{Prover, Verifier};
	use bulletproofs::BulletproofGens;
	use merlin::Transcript;
	use rand::rngs::StdRng;
	use rand::SeedableRng;
	// For benchmarking
	use std::time::Instant;

	fn get_poseidon_params() -> Poseidon {
		let width = 6;
		let (full_b, full_e) = (4, 4);
		let partial_rounds = 140;
		Poseidon::new(width, full_b, full_e, partial_rounds)
	}

	#[test]
	fn poseidon_perm() {
		let sbox_type = SboxType::Cube;
		let transcript_label = b"pos_perm";
		let poseidon = get_poseidon_params();
		let width = poseidon.width;
		let total_rounds = poseidon.get_total_rounds();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let input = (0..width)
			.map(|_| Scalar::random(&mut test_rng))
			.collect::<Vec<_>>();
		let expected_output = poseidon.permute(&input, &sbox_type);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		println!("Proving");
		let (proof, commitments) = {
			let mut prover_transcript = Transcript::new(transcript_label);
			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

			let mut comms = vec![];
			let mut allocs = vec![];

			for i in 0..width {
				let (com, var) = prover.commit(input[i].clone(), Scalar::random(&mut test_rng));
				comms.push(com);
				allocs.push(var);
			}

			assert!(Poseidon_permutation_gadget(
				&mut prover,
				allocs,
				&poseidon,
				&sbox_type,
				&expected_output
			)
			.is_ok());

			println!("For Poseidon permutation rounds {}, no of constraints is {}, no of multipliers is {}", total_rounds, &prover.num_constraints(), &prover.num_multipliers());

			let proof = prover.prove(&bp_gens).unwrap();
			(proof, comms)
		};

		println!("Verifying");

		let mut verifier_transcript = Transcript::new(transcript_label);
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let mut allocs = vec![];
		for i in 0..width {
			let v = verifier.commit(commitments[i]);
			allocs.push(v);
		}
		assert!(Poseidon_permutation_gadget(
			&mut verifier,
			allocs,
			&poseidon,
			&sbox_type,
			&expected_output
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}

	#[test]
	fn poseidon_hash_2() {
		let sbox_type = SboxType::Cube;
		let transcript_label = b"pos_hash2";
		let poseidon = get_poseidon_params();
		let total_rounds = poseidon.get_total_rounds();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let xl = Scalar::random(&mut test_rng);
		let xr = Scalar::random(&mut test_rng);
		let expected_output = poseidon.hash_2(xl, xr, &sbox_type);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		println!("Proving");
		let (proof, commitments) = {
			let mut prover_transcript = Transcript::new(transcript_label);
			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

			let mut comms = vec![];

			let (com_l, var_l) = prover.commit(xl.clone(), Scalar::random(&mut test_rng));
			comms.push(com_l);

			let (com_r, var_r) = prover.commit(xr.clone(), Scalar::random(&mut test_rng));
			comms.push(com_r);

			let num_statics = 4;
			let statics = allocate_statics_for_prover(&mut prover, num_statics);

			let start = Instant::now();
			assert!(Poseidon_hash_2_gadget(
				&mut prover,
				var_l,
				var_r,
				statics,
				&poseidon,
				&sbox_type,
				&expected_output
			)
			.is_ok());

			println!(
				"For Poseidon hash 2:1 rounds {}, no of constraints is {}, no of multipliers is {}",
				total_rounds,
				&prover.num_constraints(),
				&prover.num_multipliers()
			);

			let proof = prover.prove(&bp_gens).unwrap();

			let end = start.elapsed();

			println!("Proving time is {:?}", end);
			(proof, comms)
		};

		println!("Verifying");

		let mut verifier_transcript = Transcript::new(transcript_label);
		let mut verifier = Verifier::new(&mut verifier_transcript);

		let lv = verifier.commit(commitments[0]);
		let rv = verifier.commit(commitments[1]);

		let num_statics = 4;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let start = Instant::now();
		assert!(Poseidon_hash_2_gadget(
			&mut verifier,
			lv,
			rv,
			statics,
			&poseidon,
			&sbox_type,
			&expected_output
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
		let end = start.elapsed();

		println!("Verification time is {:?}", end);
	}

	#[test]
	fn poseidon_hash_4() {
		let sbox_type = SboxType::Cube;
		let transcript_label = b"pos_hash2";
		let poseidon = get_poseidon_params();
		let total_rounds = poseidon.get_total_rounds();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let _input = (0..4)
			.map(|_| Scalar::random(&mut test_rng))
			.collect::<Vec<_>>();
		let mut input = [Scalar::zero(); 4];
		input.copy_from_slice(_input.as_slice());
		let expected_output = poseidon.hash_4(input, &sbox_type);

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		println!("Proving");
		let (proof, commitments) = {
			let mut prover_transcript = Transcript::new(transcript_label);
			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

			let mut comms = vec![];
			let mut allocs = vec![];

			for inp in input.iter() {
				let (com, var) = prover.commit(inp.clone(), Scalar::random(&mut test_rng));
				comms.push(com);
				allocs.push(var);
			}

			let num_statics = 2;
			let statics = allocate_statics_for_prover(&mut prover, num_statics);

			let start = Instant::now();
			assert!(Poseidon_hash_4_gadget(
				&mut prover,
				allocs,
				statics,
				&poseidon,
				&sbox_type,
				&expected_output
			)
			.is_ok());

			println!(
				"For Poseidon hash 4:1 rounds {}, no of constraints is {}, no of multipliers is {}",
				total_rounds,
				&prover.num_constraints(),
				&prover.num_multipliers()
			);

			let proof = prover.prove(&bp_gens).unwrap();

			let end = start.elapsed();

			println!("Proving time is {:?}", end);
			(proof, comms)
		};

		println!("Verifying");

		let mut verifier_transcript = Transcript::new(transcript_label);
		let mut verifier = Verifier::new(&mut verifier_transcript);
		let mut allocs = vec![];
		for com in commitments {
			let v = verifier.commit(com);
			allocs.push(v);
		}

		let num_statics = 2;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let start = Instant::now();
		assert!(Poseidon_hash_4_gadget(
			&mut verifier,
			allocs,
			statics,
			&poseidon,
			&sbox_type,
			&expected_output
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
		let end = start.elapsed();

		println!("Verification time is {:?}", end);
	}
}
