use crate::poseidon_constants::{MDS_ENTRIES, ROUND_CONSTS};
use crate::sbox::{simplify_lc, SboxType};
use crate::scalar_utils::get_scalar_from_hex;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSError};
use curve25519_dalek::scalar::Scalar;

#[derive(Clone)]
pub struct Poseidon {
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

// Choice is arbitrary
pub const PADDING_CONST: u64 = 101;
pub const ZERO_CONST: u64 = 0;

impl Poseidon {
	pub fn new(
		width: usize,
		full_rounds_beginning: usize,
		full_rounds_end: usize,
		partial_rounds: usize,
	) -> Self {
		let total_rounds = full_rounds_beginning + partial_rounds + full_rounds_end;
		let round_keys = Self::gen_round_keys(width, total_rounds);
		let matrix_2 = Self::gen_MDS_matrix(width);
		Self {
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

	pub fn permute(&self, input: &[Scalar], sbox: &SboxType) -> Vec<Scalar> {
		let width = self.width;
		assert_eq!(input.len(), width);

		let full_rounds_beginning = self.full_rounds_beginning;
		let partial_rounds = self.partial_rounds;
		let full_rounds_end = self.full_rounds_end;

		let mut current_state = input.to_owned();
		let mut current_state_temp = vec![Scalar::zero(); width];

		let mut round_keys_offset = 0;

		for _ in 0..full_rounds_beginning {
			for i in 0..width {
				current_state[i] += self.round_keys[round_keys_offset];
				current_state[i] = sbox.apply_sbox(&current_state[i]);
				round_keys_offset += 1;
			}

			for j in 0..width {
				for i in 0..width {
					current_state_temp[i] += current_state[j] * self.MDS_matrix[i][j];
				}
			}

			for i in 0..width {
				current_state[i] = current_state_temp[i];
				current_state_temp[i] = Scalar::zero();
			}
		}

		for _ in full_rounds_beginning..(full_rounds_beginning + partial_rounds) {
			for i in 0..width {
				current_state[i] += &self.round_keys[round_keys_offset];
				round_keys_offset += 1;
			}
			current_state[width - 1] = sbox.apply_sbox(&current_state[width - 1]);

			for j in 0..width {
				for i in 0..width {
					current_state_temp[i] += current_state[j] * self.MDS_matrix[i][j];
				}
			}

			for i in 0..width {
				current_state[i] = current_state_temp[i];
				current_state_temp[i] = Scalar::zero();
			}
		}

		for _ in full_rounds_beginning + partial_rounds
			..(full_rounds_beginning + partial_rounds + full_rounds_end)
		{
			for i in 0..width {
				current_state[i] += self.round_keys[round_keys_offset];
				current_state[i] = sbox.apply_sbox(&current_state[i]);
				round_keys_offset += 1;
			}

			for j in 0..width {
				for i in 0..width {
					current_state_temp[i] += current_state[j] * self.MDS_matrix[i][j];
				}
			}

			for i in 0..width {
				current_state[i] = current_state_temp[i];
				current_state_temp[i] = Scalar::zero();
			}
		}

		current_state
	}

	pub fn permute_constraints<'a, CS: ConstraintSystem>(
		&self,
		cs: &mut CS,
		input: Vec<LinearCombination>,
		sbox_type: &SboxType,
	) -> Result<Vec<LinearCombination>, R1CSError> {
		let width = self.width;
		assert_eq!(input.len(), width);
		let mut input_vars: Vec<LinearCombination> = input;

		let mut round_keys_offset = 0;

		let full_rounds_beginning = self.full_rounds_beginning;
		let partial_rounds = self.partial_rounds;
		let full_rounds_end = self.full_rounds_end;

		for k in 0..full_rounds_beginning {
			let mut sbox_outputs: Vec<LinearCombination> =
				vec![LinearCombination::default(); width];

			for i in 0..width {
				let round_key = self.round_keys[round_keys_offset];
				sbox_outputs[i] = sbox_type
					.synthesize_sbox(cs, input_vars[i].clone(), round_key)?
					.into();

				round_keys_offset += 1;
			}

			let mut next_input_vars: Vec<LinearCombination> =
				vec![LinearCombination::default(); width];

			for j in 0..width {
				for i in 0..width {
					next_input_vars[i] = next_input_vars[i].clone()
						+ sbox_outputs[j].clone() * self.MDS_matrix[i][j];
				}
			}
			for i in 0..width {
				input_vars[i] = next_input_vars.remove(0);
			}
		}

		for k in full_rounds_beginning..(full_rounds_beginning + partial_rounds) {
			let mut sbox_outputs: Vec<LinearCombination> =
				vec![LinearCombination::default(); width];
			for i in 0..width {
				let round_key = self.round_keys[round_keys_offset];
				if i == width - 1 {
					sbox_outputs[i] = sbox_type
						.synthesize_sbox(cs, input_vars[i].clone(), round_key)?
						.into();
				} else {
					sbox_outputs[i] = input_vars[i].clone() + LinearCombination::from(round_key);
				}

				round_keys_offset += 1;
			}

			let mut next_input_vars: Vec<LinearCombination> =
				vec![LinearCombination::default(); width];

			for j in 0..width {
				for i in 0..width {
					next_input_vars[i] = next_input_vars[i].clone()
						+ sbox_outputs[j].clone() * self.MDS_matrix[i][j];
				}
			}

			for i in 0..width {
				input_vars[i] = simplify_lc(next_input_vars.remove(0));
			}
		}

		for k in (full_rounds_beginning + partial_rounds)
			..(full_rounds_beginning + partial_rounds + full_rounds_end)
		{
			let mut sbox_outputs: Vec<LinearCombination> =
				vec![LinearCombination::default(); width];
			for i in 0..width {
				let round_key = self.round_keys[round_keys_offset];
				sbox_outputs[i] = sbox_type
					.synthesize_sbox(cs, input_vars[i].clone(), round_key)?
					.into();

				round_keys_offset += 1;
			}

			let mut next_input_vars: Vec<LinearCombination> =
				vec![LinearCombination::default(); width];

			for j in 0..width {
				for i in 0..width {
					next_input_vars[i] = next_input_vars[i].clone()
						+ sbox_outputs[j].clone() * self.MDS_matrix[i][j];
				}
			}

			for i in 0..width {
				input_vars[i] = next_input_vars.remove(0);
			}
		}

		Ok(input_vars)
	}

	pub fn hash_2_constraints<'a, CS: ConstraintSystem>(
		&self,
		cs: &mut CS,
		xl: LinearCombination,
		xr: LinearCombination,
		statics: Vec<LinearCombination>,
		sbox_type: &SboxType,
	) -> Result<LinearCombination, R1CSError> {
		let width = self.width;
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
		let permutation_output = self.permute_constraints::<CS>(cs, inputs, sbox_type)?;
		Ok(permutation_output[1].to_owned())
	}

	pub fn hash_4_constraints<'a, CS: ConstraintSystem>(
		&self,
		cs: &mut CS,
		input: [LinearCombination; 4],
		statics: Vec<LinearCombination>,
		sbox_type: &SboxType,
	) -> Result<LinearCombination, R1CSError> {
		let width = self.width;
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
		let permutation_output = self.permute_constraints::<CS>(cs, inputs, sbox_type)?;
		Ok(permutation_output[1].to_owned())
	}

	pub fn hash_2(&self, xl: Scalar, xr: Scalar, sbox: &SboxType) -> Scalar {
		let input = vec![
			Scalar::from(ZERO_CONST),
			xl,
			xr,
			Scalar::from(PADDING_CONST),
			Scalar::from(ZERO_CONST),
			Scalar::from(ZERO_CONST),
		];
		self.permute(&input, sbox)[1]
	}

	pub fn hash_4(&self, inputs: [Scalar; 4], sbox: &SboxType) -> Scalar {
		let input = vec![
			Scalar::from(ZERO_CONST),
			inputs[0],
			inputs[1],
			inputs[2],
			inputs[3],
			Scalar::from(PADDING_CONST),
		];

		self.permute(&input, sbox)[1]
	}
}
