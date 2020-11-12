use bulletproofs::r1cs::LinearCombination;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

/// if x == 0 then y = 0 else y = 1
/// if x != 0 then inv = x^-1 else inv = 0
/// x*(1-y) = 0
/// x*inv = y
/// The idea is described in the Pinocchio paper and i first saw it in https://github.com/HarryR/ethsnarks/blob/master/src/gadgets/isnonzero.cpp

/// Enforces that x is 0.
pub fn is_zero_gadget<CS: ConstraintSystem>(cs: &mut CS, x: Variable) -> Result<(), R1CSError> {
	let y: u32 = 0;
	let inv: u32 = 0;

	let x_lc: LinearCombination = vec![(x, Scalar::one())].iter().collect();
	let one_minus_y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(1 - y))]
		.iter()
		.collect();
	let y_lc: LinearCombination = vec![(Variable::One(), Scalar::from(y))].iter().collect();
	let inv_lc: LinearCombination = vec![(Variable::One(), Scalar::from(inv))].iter().collect();

	// x * (1-y) = 0
	let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
	cs.constrain(o1.into());

	// x * inv = y
	let (_, _, o2) = cs.multiply(x_lc, inv_lc);
	// Output wire should have value `y`
	cs.constrain(o2 - y_lc);

	Ok(())
}
