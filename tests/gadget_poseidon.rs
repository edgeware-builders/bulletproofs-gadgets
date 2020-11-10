#![allow(non_snake_case)]
//extern crate spock;
use bulletproofs::poseidon::{
	allocate_statics_for_prover, allocate_statics_for_verifier, PoseidonParams, Poseidon_hash_2,
	Poseidon_hash_2_gadget, Poseidon_hash_4, Poseidon_hash_4_gadget, Poseidon_permutation,
	Poseidon_permutation_gadget, SboxType,
};
use bulletproofs::r1cs::{Prover, Verifier};
use bulletproofs::r1cs_utils::AllocatedScalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::StdRng;
use rand::SeedableRng;

#[cfg(test)]
mod tests {
	use super::*;
	// For benchmarking
	use std::time::Instant;

	fn get_poseidon_params() -> PoseidonParams {
		let width = 6;
		let (full_b, full_e) = (4, 4);
		let partial_rounds = 140;
		PoseidonParams::new(width, full_b, full_e, partial_rounds)
	}

	fn poseidon_perm(sbox_type: &SboxType, transcript_label: &'static [u8]) {
		let s_params = get_poseidon_params();
		let width = s_params.width;
		let total_rounds = s_params.get_total_rounds();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let input = (0..width)
			.map(|_| Scalar::random(&mut test_rng))
			.collect::<Vec<_>>();
		let expected_output = Poseidon_permutation(&input, &s_params, sbox_type);

		/*println!("Input:\n");
		println!("{:?}", &input);
		println!("Expected output:\n");
		println!("{:?}", &expected_output);*/

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
				allocs.push(AllocatedScalar {
					variable: var,
					assignment: Some(input[i]),
				});
			}

			assert!(Poseidon_permutation_gadget(
				&mut prover,
				allocs,
				&s_params,
				sbox_type,
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
			allocs.push(AllocatedScalar {
				variable: v,
				assignment: None,
			});
		}
		assert!(Poseidon_permutation_gadget(
			&mut verifier,
			allocs,
			&s_params,
			sbox_type,
			&expected_output
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
	}

	fn poseidon_hash_2(sbox_type: &SboxType, transcript_label: &'static [u8]) {
		let s_params = get_poseidon_params();
		let total_rounds = s_params.get_total_rounds();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let xl = Scalar::random(&mut test_rng);
		let xr = Scalar::random(&mut test_rng);
		let expected_output = Poseidon_hash_2(xl, xr, &s_params, sbox_type);

		/*println!("Input:\n");
		println!("xl={:?}", &xl);
		println!("xr={:?}", &xr);
		println!("Expected output:\n");
		println!("{:?}", &expected_output);*/

		let pc_gens = PedersenGens::default();
		let bp_gens = BulletproofGens::new(2048, 1);

		println!("Proving");
		let (proof, commitments) = {
			let mut prover_transcript = Transcript::new(transcript_label);
			let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

			let mut comms = vec![];

			let (com_l, var_l) = prover.commit(xl.clone(), Scalar::random(&mut test_rng));
			comms.push(com_l);
			let l_alloc = AllocatedScalar {
				variable: var_l,
				assignment: Some(xl),
			};

			let (com_r, var_r) = prover.commit(xr.clone(), Scalar::random(&mut test_rng));
			comms.push(com_r);
			let r_alloc = AllocatedScalar {
				variable: var_r,
				assignment: Some(xr),
			};

			let num_statics = 4;
			let statics = allocate_statics_for_prover(&mut prover, num_statics);

			let start = Instant::now();
			assert!(Poseidon_hash_2_gadget(
				&mut prover,
				l_alloc,
				r_alloc,
				statics,
				&s_params,
				sbox_type,
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
		let l_alloc = AllocatedScalar {
			variable: lv,
			assignment: None,
		};
		let r_alloc = AllocatedScalar {
			variable: rv,
			assignment: None,
		};

		let num_statics = 4;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let start = Instant::now();
		assert!(Poseidon_hash_2_gadget(
			&mut verifier,
			l_alloc,
			r_alloc,
			statics,
			&s_params,
			sbox_type,
			&expected_output
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
		let end = start.elapsed();

		println!("Verification time is {:?}", end);
	}

	fn poseidon_hash_4(sbox_type: &SboxType, transcript_label: &'static [u8]) {
		let s_params = get_poseidon_params();
		let total_rounds = s_params.get_total_rounds();

		let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		let _input = (0..4)
			.map(|_| Scalar::random(&mut test_rng))
			.collect::<Vec<_>>();
		let mut input = [Scalar::zero(); 4];
		input.copy_from_slice(_input.as_slice());
		let expected_output = Poseidon_hash_4(input, &s_params, sbox_type);

		/*println!("Input:\n");
		println!("xl={:?}", &xl);
		println!("xr={:?}", &xr);
		println!("Expected output:\n");
		println!("{:?}", &expected_output);*/

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
				allocs.push(AllocatedScalar {
					variable: var,
					assignment: Some(inp.clone()),
				});
			}

			let num_statics = 2;
			let statics = allocate_statics_for_prover(&mut prover, num_statics);

			let start = Instant::now();
			assert!(Poseidon_hash_4_gadget(
				&mut prover,
				allocs,
				statics,
				&s_params,
				sbox_type,
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
			allocs.push({
				AllocatedScalar {
					variable: v,
					assignment: None,
				}
			});
		}

		let num_statics = 2;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let start = Instant::now();
		assert!(Poseidon_hash_4_gadget(
			&mut verifier,
			allocs,
			statics,
			&s_params,
			sbox_type,
			&expected_output
		)
		.is_ok());

		assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
		let end = start.elapsed();

		println!("Verification time is {:?}", end);
	}

	#[test]
	fn test_poseidon_perm_cube_sbox() {
		poseidon_perm(&SboxType::Cube, b"Poseidon_perm_cube");
	}

	#[test]
	fn test_poseidon_perm_inverse_sbox() {
		poseidon_perm(&SboxType::Inverse, b"Poseidon_perm_inverse");
	}

	#[test]
	fn test_poseidon_hash_2_cube_sbox() {
		poseidon_hash_2(&SboxType::Cube, b"Poseidon_hash_2_cube");
	}

	#[test]
	fn test_poseidon_hash_2_inverse_sbox() {
		poseidon_hash_2(&SboxType::Inverse, b"Poseidon_hash_2_inverse");
	}

	#[test]
	fn test_poseidon_hash_4_cube_sbox() {
		poseidon_hash_4(&SboxType::Cube, b"Poseidon_hash_2_cube");
	}

	#[test]
	fn test_poseidon_hash_4_inverse_sbox() {
		poseidon_hash_4(&SboxType::Inverse, b"Poseidon_hash_2_inverse");
	}
}
