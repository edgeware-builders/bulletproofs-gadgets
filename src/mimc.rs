use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSError, Variable};
use curve25519_dalek::scalar::Scalar;

//pub const MIMC_ROUNDS: usize = 322;
pub const MIMC_ROUNDS: usize = 10;

pub fn mimc(xl: &Scalar, xr: &Scalar, constants: &[Scalar]) -> Scalar {
	assert_eq!(constants.len(), MIMC_ROUNDS);

	let mut xl = xl.clone();
	let mut xr = xr.clone();

	for i in 0..MIMC_ROUNDS {
		let tmp1 = xl + constants[i];
		let mut tmp2 = (tmp1 * tmp1) * tmp1;
		tmp2 += xr;
		xr = xl;
		xl = tmp2;
	}

	xl
}

pub fn mimc_constraints<CS: ConstraintSystem>(
	cs: &mut CS,
	xl: &LinearCombination,
	xr: &LinearCombination,
	constants: &[Scalar],
) -> LinearCombination {
	assert_eq!(constants.len(), MIMC_ROUNDS);

	let mut xl = xl.clone();
	let mut xr = xr.clone();

	for i in 0..MIMC_ROUNDS {
		let tmp1 = xl.clone() + constants[i];
		let (_, _, tmp2_m) = cs.multiply(tmp1.clone(), tmp1.clone());
		let (_, _, tmp2) = cs.multiply(tmp2_m.into(), tmp1);
		let tmp2 = tmp2 + xr;
		xr = xl;
		xl = tmp2;
	}

	xl
}
