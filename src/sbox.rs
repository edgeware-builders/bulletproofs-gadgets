use crate::gadget_not_equals::is_nonzero_gadget;
use bulletproofs::r1cs::{
	ConstraintSystem, LinearCombination, Prover, R1CSError, Variable, Verifier,
};
use curve25519_dalek::scalar::Scalar;
use std::collections::HashMap;

/// Simplify linear combination by taking Variables common across terms and adding their corresponding scalars.
/// Useful when linear combinations become large. Takes ownership of linear combination as this function is useful
/// when memory is limited and the obvious action after this function call will be to free the memory held by the passed linear combination
pub fn simplify_lc(lc: LinearCombination) -> LinearCombination {
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
	pub fn apply_sbox(&self, elem: &Scalar) -> Scalar {
		match self {
			SboxType::Cube => (elem * elem) * elem,
			SboxType::Inverse => elem.invert(),
		}
	}

	pub fn synthesize_sbox<CS: ConstraintSystem>(
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
	pub fn synthesize_cube_sbox<CS: ConstraintSystem>(
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
