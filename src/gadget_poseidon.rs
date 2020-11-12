#![allow(non_snake_case)]
use crate::gadget_not_equals::is_nonzero_gadget;
use crate::poseidon_constants::{MDS_ENTRIES, ROUND_CONSTS};
use crate::scalar_utils::get_scalar_from_hex;
use bulletproofs::r1cs::{
	ConstraintSystem, LinearCombination, Prover, R1CSError, Variable, Verifier,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::collections::HashMap;

#[derive(Clone)]
pub struct PoseidonParams {
	pub width: usize,
	// Number of full SBox rounds in beginning
	pub full_rounds_beginning: usize,
	// Number of full SBox rounds in end
	pub full_rounds_end: usize,
	// Number of partial SBox rounds in beginning
	pub partial_rounds: usize,
	pub round_keys: Vec<Scalar>,
	pub MDS_matrix: Vec<Vec<Scalar>>,
}

impl PoseidonParams {
	pub fn new(
		width: usize,
		full_rounds_beginning: usize,
		full_rounds_end: usize,
		partial_rounds: usize,
	) -> PoseidonParams {
		let total_rounds = full_rounds_beginning + partial_rounds + full_rounds_end;
		let round_keys = Self::gen_round_keys(width, total_rounds);
		let matrix_2 = Self::gen_MDS_matrix(width);
		PoseidonParams {
			width,
			full_rounds_beginning,
			full_rounds_end,
			partial_rounds,
			round_keys,
			MDS_matrix: matrix_2,
		}
	}

	// TODO: Write logic to generate correct round keys.
	fn gen_round_keys(width: usize, total_rounds: usize) -> Vec<Scalar> {
		let cap = total_rounds * width;
		/*let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		vec![Scalar::random(&mut test_rng); cap]*/
		if ROUND_CONSTS.len() < cap {
			panic!(
				"Not enough round constants, need {}, found {}",
				cap,
				ROUND_CONSTS.len()
			);
		}
		let mut rc = vec![];
		for i in 0..cap {
			// TODO: Remove unwrap, handle error
			let c = get_scalar_from_hex(ROUND_CONSTS[i]).unwrap();
			rc.push(c);
		}
		rc
	}

	// TODO: Write logic to generate correct MDS matrix. Currently loading hardcoded constants.
	fn gen_MDS_matrix(width: usize) -> Vec<Vec<Scalar>> {
		/*let mut test_rng: StdRng = SeedableRng::from_seed([24u8; 32]);
		vec![vec![Scalar::random(&mut test_rng); width]; width]*/
		if MDS_ENTRIES.len() != width {
			panic!("Incorrect width, only width {} is supported now", width);
		}
		let mut mds: Vec<Vec<Scalar>> = vec![vec![Scalar::zero(); width]; width];
		for i in 0..width {
			if MDS_ENTRIES[i].len() != width {
				panic!("Incorrect width, only width {} is supported now", width);
			}
			for j in 0..width {
				// TODO: Remove unwrap, handle error
				mds[i][j] = get_scalar_from_hex(MDS_ENTRIES[i][j]).unwrap();
			}
		}
		mds
	}

	pub fn get_total_rounds(&self) -> usize {
		self.full_rounds_beginning + self.partial_rounds + self.full_rounds_end
	}
}

/// Simplify linear combination by taking Variables common across terms and adding their corresponding scalars.
/// Useful when linear combinations become large. Takes ownership of linear combination as this function is useful
/// when memory is limited and the obvious action after this function call will be to free the memory held by the passed linear combination
fn simplify_lc(lc: LinearCombination) -> LinearCombination {
	// TODO: Move this code to the fork of bulletproofs
	let mut vars: HashMap<Variable, Scalar> = HashMap::new();
	let terms = lc.get_terms();
	for (var, val) in terms {
		*vars.entry(var).or_insert(Scalar::zero()) += val;
	}

	let mut new_lc_terms = vec![];
	for (var, val) in vars {
		new_lc_terms.push((var, val));
	}
	new_lc_terms.iter().collect()
}

pub enum SboxType {
	Cube,
	Inverse,
}

impl SboxType {
	fn apply_sbox(&self, elem: &Scalar) -> Scalar {
		match self {
			SboxType::Cube => (elem * elem) * elem,
			SboxType::Inverse => elem.invert(),
		}
	}

	fn synthesize_sbox<CS: ConstraintSystem>(
		&self,
		cs: &mut CS,
		input_var: LinearCombination,
		round_key: Scalar,
	) -> Result<Variable, R1CSError> {
		match self {
			SboxType::Cube => Self::synthesize_cube_sbox(cs, input_var, round_key),
			SboxType::Inverse => Self::synthesize_inverse_sbox(cs, input_var, round_key),
			_ => Err(R1CSError::GadgetError {
				description: String::from("Unknown Sbox type"),
			}),
		}
	}

	// Allocate variables in circuit and enforce constraints when Sbox as cube
	fn synthesize_cube_sbox<CS: ConstraintSystem>(
		cs: &mut CS,
		input_var: LinearCombination,
		round_key: Scalar,
	) -> Result<Variable, R1CSError> {
		let inp_plus_const: LinearCombination = input_var + round_key;
		let (i, _, sqr) = cs.multiply(inp_plus_const.clone(), inp_plus_const);
		let (_, _, cube) = cs.multiply(sqr.into(), i.into());
		Ok(cube)
	}

	// Allocate variables in circuit and enforce constraints when Sbox as inverse
	fn synthesize_inverse_sbox<CS: ConstraintSystem>(
		cs: &mut CS,
		input_var: LinearCombination,
		round_key: Scalar,
	) -> Result<Variable, R1CSError> {
		let inp_plus_const: LinearCombination = input_var + round_key;

		let val_l = cs.evaluate_lc(&inp_plus_const);
		let val_r = val_l.map(|l| l.invert());

		let (var_l, _) = cs.allocate_single(val_l)?;
		let (var_r, var_o) = cs.allocate_single(val_r)?;

		// Ensure `inp_plus_const` is not zero. As a side effect, `is_nonzero_gadget` also ensures that arguments passes are inverse of each other
		is_nonzero_gadget(cs, var_l, var_r)?;

		// Constrain product of `inp_plus_const` and its inverse to be 1.
		cs.constrain(var_o.unwrap() - 1u64);

		Ok(var_r)
	}
}

pub fn Poseidon_permutation(
	input: &[Scalar],
	params: &PoseidonParams,
	sbox: &SboxType,
) -> Vec<Scalar> {
	let width = params.width;
	assert_eq!(input.len(), width);

	let full_rounds_beginning = params.full_rounds_beginning;
	let partial_rounds = params.partial_rounds;
	let full_rounds_end = params.full_rounds_end;

	let mut current_state = input.to_owned();
	let mut current_state_temp = vec![Scalar::zero(); width];

	let mut round_keys_offset = 0;

	// full Sbox rounds
	for _ in 0..full_rounds_beginning {
		// Sbox layer
		for i in 0..width {
			current_state[i] += params.round_keys[round_keys_offset];
			current_state[i] = sbox.apply_sbox(&current_state[i]);
			round_keys_offset += 1;
		}

		// linear layer
		for j in 0..width {
			for i in 0..width {
				current_state_temp[i] += current_state[j] * params.MDS_matrix[i][j];
			}
		}

		// Output of this round becomes input to next round
		for i in 0..width {
			current_state[i] = current_state_temp[i];
			current_state_temp[i] = Scalar::zero();
		}
	}

	// middle partial Sbox rounds
	for _ in full_rounds_beginning..(full_rounds_beginning + partial_rounds) {
		for i in 0..width {
			current_state[i] += &params.round_keys[round_keys_offset];
			round_keys_offset += 1;
		}

		// partial Sbox layer, apply Sbox to only 1 element of the state.
		// Here the last one is chosen but the choice is arbitrary.
		current_state[width - 1] = sbox.apply_sbox(&current_state[width - 1]);

		// linear layer
		for j in 0..width {
			for i in 0..width {
				current_state_temp[i] += current_state[j] * params.MDS_matrix[i][j];
			}
		}

		// Output of this round becomes input to next round
		for i in 0..width {
			current_state[i] = current_state_temp[i];
			current_state_temp[i] = Scalar::zero();
		}
	}

	// last full Sbox rounds
	for _ in full_rounds_beginning + partial_rounds
		..(full_rounds_beginning + partial_rounds + full_rounds_end)
	{
		// Sbox layer
		for i in 0..width {
			current_state[i] += params.round_keys[round_keys_offset];
			current_state[i] = sbox.apply_sbox(&current_state[i]);
			round_keys_offset += 1;
		}

		// linear layer
		for j in 0..width {
			for i in 0..width {
				current_state_temp[i] += current_state[j] * params.MDS_matrix[i][j];
			}
		}

		// Output of this round becomes input to next round
		for i in 0..width {
			current_state[i] = current_state_temp[i];
			current_state_temp[i] = Scalar::zero();
		}
	}

	// Finally the current_state becomes the output
	current_state
}

pub fn Poseidon_permutation_constraints<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	input: Vec<LinearCombination>,
	params: &'a PoseidonParams,
	sbox_type: &SboxType,
) -> Result<Vec<LinearCombination>, R1CSError> {
	let width = params.width;
	assert_eq!(input.len(), width);

	fn apply_linear_layer(
		width: usize,
		sbox_outs: Vec<LinearCombination>,
		next_inputs: &mut Vec<LinearCombination>,
		MDS_matrix: &Vec<Vec<Scalar>>,
	) {
		for j in 0..width {
			for i in 0..width {
				next_inputs[i] = next_inputs[i].clone() + sbox_outs[j].clone() * MDS_matrix[i][j];
			}
		}
	}

	let mut input_vars: Vec<LinearCombination> = input;

	let mut round_keys_offset = 0;

	let full_rounds_beginning = params.full_rounds_beginning;
	let partial_rounds = params.partial_rounds;
	let full_rounds_end = params.full_rounds_end;

	// ------------ First rounds with full SBox begin --------------------

	for k in 0..full_rounds_beginning {
		let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); width];

		// Substitution (S-box) layer
		for i in 0..width {
			let round_key = params.round_keys[round_keys_offset];
			sbox_outputs[i] = sbox_type
				.synthesize_sbox(cs, input_vars[i].clone(), round_key)?
				.into();

			round_keys_offset += 1;
		}

		let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); width];

		apply_linear_layer(
			width,
			sbox_outputs,
			&mut next_input_vars,
			&params.MDS_matrix,
		);

		for i in 0..width {
			// replace input_vars with next_input_vars
			input_vars[i] = next_input_vars.remove(0);
		}
	}

	// ------------ First rounds with full SBox begin --------------------

	// ------------ Middle rounds with partial SBox begin --------------------

	for k in full_rounds_beginning..(full_rounds_beginning + partial_rounds) {
		let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); width];

		// Substitution (S-box) layer
		for i in 0..width {
			let round_key = params.round_keys[round_keys_offset];

			// apply Sbox to only 1 element of the state.
			// Here the last one is chosen but the choice is arbitrary.
			if i == width - 1 {
				sbox_outputs[i] = sbox_type
					.synthesize_sbox(cs, input_vars[i].clone(), round_key)?
					.into();
			} else {
				sbox_outputs[i] = input_vars[i].clone() + LinearCombination::from(round_key);
			}

			round_keys_offset += 1;
		}

		// Linear layer

		let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); width];

		apply_linear_layer(
			width,
			sbox_outputs,
			&mut next_input_vars,
			&params.MDS_matrix,
		);

		for i in 0..width {
			// replace input_vars with simplified next_input_vars
			input_vars[i] = simplify_lc(next_input_vars.remove(0));
		}
	}

	// ------------ Middle rounds with partial SBox end --------------------

	// ------------ Last rounds with full SBox begin --------------------

	for k in (full_rounds_beginning + partial_rounds)
		..(full_rounds_beginning + partial_rounds + full_rounds_end)
	{
		let mut sbox_outputs: Vec<LinearCombination> = vec![LinearCombination::default(); width];

		// Substitution (S-box) layer
		for i in 0..width {
			let round_key = params.round_keys[round_keys_offset];
			sbox_outputs[i] = sbox_type
				.synthesize_sbox(cs, input_vars[i].clone(), round_key)?
				.into();

			round_keys_offset += 1;
		}

		// Linear layer

		let mut next_input_vars: Vec<LinearCombination> = vec![LinearCombination::default(); width];

		apply_linear_layer(
			width,
			sbox_outputs,
			&mut next_input_vars,
			&params.MDS_matrix,
		);

		for i in 0..width {
			// replace input_vars with next_input_vars
			input_vars[i] = next_input_vars.remove(0);
		}
	}

	// ------------ Last rounds with full SBox end --------------------

	Ok(input_vars)
}

pub fn Poseidon_permutation_gadget<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	input: Vec<Variable>,
	params: &'a PoseidonParams,
	sbox_type: &SboxType,
	output: &[Scalar],
) -> Result<(), R1CSError> {
	let width = params.width;
	assert_eq!(output.len(), width);

	let input_vars: Vec<LinearCombination> = input.iter().map(|&e| e.into()).collect();
	let permutation_output =
		Poseidon_permutation_constraints::<CS>(cs, input_vars, params, sbox_type)?;

	for i in 0..width {
		cs.constrain(permutation_output[i].to_owned() - output[i]);
	}

	Ok(())
}

/// 2:1 (2 inputs, 1 output) hash from the permutation by passing the first input as zero, 2 of the next 4 as non-zero, a padding constant and rest zero. Choose one of the outputs.

// Choice is arbitrary
pub const PADDING_CONST: u64 = 101;
pub const ZERO_CONST: u64 = 0;

pub fn Poseidon_hash_2(xl: Scalar, xr: Scalar, params: &PoseidonParams, sbox: &SboxType) -> Scalar {
	// Only 2 inputs to the permutation are set to the input of this hash function,
	// one is set to the padding constant and rest are 0. Always keep the 1st input as 0

	let input = vec![
		Scalar::from(ZERO_CONST),
		xl,
		xr,
		Scalar::from(PADDING_CONST),
		Scalar::from(ZERO_CONST),
		Scalar::from(ZERO_CONST),
	];

	// Never take the first output
	Poseidon_permutation(&input, params, sbox)[1]
}

pub fn Poseidon_hash_2_constraints<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	xl: LinearCombination,
	xr: LinearCombination,
	statics: Vec<LinearCombination>,
	params: &'a PoseidonParams,
	sbox_type: &SboxType,
) -> Result<LinearCombination, R1CSError> {
	let width = params.width;
	// Only 2 inputs to the permutation are set to the input of this hash function.
	assert_eq!(statics.len(), width - 2);

	// Always keep the 1st input as 0
	let mut inputs = vec![statics[0].to_owned()];
	inputs.push(xl);
	inputs.push(xr);

	// statics correspond to committed variables with values as PADDING_CONST and 0s and randomness as 0
	for i in 1..statics.len() {
		inputs.push(statics[i].to_owned());
	}
	let permutation_output = Poseidon_permutation_constraints::<CS>(cs, inputs, params, sbox_type)?;
	Ok(permutation_output[1].to_owned())
}

pub fn Poseidon_hash_2_gadget<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	xl: Variable,
	xr: Variable,
	statics: Vec<Variable>,
	params: &'a PoseidonParams,
	sbox_type: &SboxType,
	output: &Scalar,
) -> Result<(), R1CSError> {
	let statics: Vec<LinearCombination> = statics.iter().map(|&s| s.into()).collect();
	let hash =
		Poseidon_hash_2_constraints::<CS>(cs, xl.into(), xr.into(), statics, params, sbox_type)?;

	cs.constrain(hash - *output);

	Ok(())
}

pub fn Poseidon_hash_4(inputs: [Scalar; 4], params: &PoseidonParams, sbox: &SboxType) -> Scalar {
	// Only 4 inputs to the permutation are set to the input of this hash function,
	// one is set to the padding constant and one is set to 0. Always keep the 1st input as 0

	let input = vec![
		Scalar::from(ZERO_CONST),
		inputs[0],
		inputs[1],
		inputs[2],
		inputs[3],
		Scalar::from(PADDING_CONST),
	];

	// Never take the first output
	Poseidon_permutation(&input, params, sbox)[1]
}

pub fn Poseidon_hash_4_constraints<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	input: [LinearCombination; 4],
	statics: Vec<LinearCombination>,
	params: &'a PoseidonParams,
	sbox_type: &SboxType,
) -> Result<LinearCombination, R1CSError> {
	let width = params.width;
	// Only 4 inputs to the permutation are set to the input of this hash function.
	assert_eq!(statics.len(), width - 4);

	// Always keep the 1st input as 0
	let mut inputs = vec![statics[0].to_owned()];
	inputs.push(input[0].clone());
	inputs.push(input[1].clone());
	inputs.push(input[2].clone());
	inputs.push(input[3].clone());

	// statics correspond to committed variables with values as PADDING_CONST and 0s and randomness as 0
	for i in 1..statics.len() {
		inputs.push(statics[i].to_owned());
	}
	let permutation_output = Poseidon_permutation_constraints::<CS>(cs, inputs, params, sbox_type)?;
	Ok(permutation_output[1].to_owned())
}

pub fn Poseidon_hash_4_gadget<'a, CS: ConstraintSystem>(
	cs: &mut CS,
	input: Vec<Variable>,
	statics: Vec<Variable>,
	params: &'a PoseidonParams,
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
	let hash = Poseidon_hash_4_constraints::<CS>(cs, input_arr, statics, params, sbox_type)?;

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
			allocs.push(v);
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

		let num_statics = 4;
		let statics = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

		let start = Instant::now();
		assert!(Poseidon_hash_2_gadget(
			&mut verifier,
			lv,
			rv,
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
			allocs.push(v);
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
