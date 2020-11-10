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
