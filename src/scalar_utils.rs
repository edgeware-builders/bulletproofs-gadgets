use curve25519_dalek::scalar::Scalar;
use std::fmt;
use std::num::ParseIntError;
pub type ScalarBytes = [u8; 32];

pub const TREE_DEPTH: usize = 253;

/// Get a 253 elem bit array of this scalar, LSB is first element of this array
#[derive(Copy, Clone)]
pub struct ScalarBits {
	bit_array: [i8; TREE_DEPTH],
}

impl fmt::Debug for ScalarBits {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:?}", self.bit_array.to_vec())
	}
}

impl ScalarBits {
	pub fn from_scalar(scalar: &Scalar) -> Self {
		let s = scalar.reduce();
		let b = get_bits(&s);
		for i in TREE_DEPTH..256 {
			assert_eq!(b[i], 0);
		}

		let mut reduced_bits = [0; TREE_DEPTH];
		for i in 0..TREE_DEPTH {
			reduced_bits[i] = b[i];
		}
		Self {
			bit_array: reduced_bits,
		}
	}

	pub fn from_scalar_dont_reduce(scalar: &Scalar) -> Self {
		//let s = scalar.reduce();
		let b = get_bits(scalar);
		for i in TREE_DEPTH..256 {
			assert_eq!(b[i], 0);
		}

		let mut reduced_bits = [0; TREE_DEPTH];
		for i in 0..TREE_DEPTH {
			reduced_bits[i] = b[i];
		}
		Self {
			bit_array: reduced_bits,
		}
	}

	pub fn to_scalar(&self) -> Scalar {
		/*let mut bytes: [u8; 32] = [0; 32];
		let powers_of_2: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
		let mut i = 0;
		let mut current_byte = 0u8;
		for b in self.bit_array.iter() {
			if *b == 1 {
				current_byte += powers_of_2[i % 8];
			}
			i += 1;
			if (i % 8) == 0 {
				bytes[(i / 8) -1] = current_byte;
				current_byte = 0;
			}
		}
		bytes[31] = current_byte;
		Scalar::from_bits(bytes).reduce()*/
		self.to_non_reduced_scalar().reduce()
	}

	pub fn to_non_reduced_scalar(&self) -> Scalar {
		let mut bytes: [u8; 32] = [0; 32];
		let powers_of_2: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
		let mut i = 0;
		let mut current_byte = 0u8;
		for b in self.bit_array.iter() {
			if *b == 1 {
				current_byte += powers_of_2[i % 8];
			}
			i += 1;
			if (i % 8) == 0 {
				bytes[(i / 8) - 1] = current_byte;
				current_byte = 0;
			}
		}
		bytes[31] = current_byte;
		Scalar::from_bits(bytes)
	}

	pub fn shl(&mut self) {
		for i in (1..TREE_DEPTH).rev() {
			self.bit_array[i] = self.bit_array[i - 1];
		}
		self.bit_array[0] = 0;
	}

	pub fn shr(&mut self) {
		for i in 1..TREE_DEPTH {
			self.bit_array[i - 1] = self.bit_array[i];
		}
		self.bit_array[TREE_DEPTH - 1] = 0;
	}

	pub fn new_left_shifted(&self) -> Self {
		// Not using the above method `shl` to avoid copying
		let mut new_array = [0; TREE_DEPTH];
		for i in (1..TREE_DEPTH).rev() {
			new_array[i] = self.bit_array[i - 1];
		}
		new_array[0] = 0;
		Self {
			bit_array: new_array,
		}
	}

	pub fn new_right_shifted(&self) -> Self {
		// Not using the above method `shr` to avoid copying
		let mut new_array = [0; TREE_DEPTH];
		for i in 1..TREE_DEPTH {
			new_array[i - 1] = self.bit_array[i];
		}
		new_array[TREE_DEPTH - 1] = 0;
		Self {
			bit_array: new_array,
		}
	}

	pub fn is_msb_set(&self) -> bool {
		self.bit_array[TREE_DEPTH - 1] == 1
	}

	pub fn is_lsb_set(&self) -> bool {
		self.bit_array[0] == 1
	}
}

pub fn get_bits(scalar: &Scalar) -> [i8; 256] {
	let mut bits = [0i8; 256];
	let bytes = scalar.as_bytes();
	for i in 0..256 {
		// As i runs from 0..256, the bottom 3 bits index the bit,
		// while the upper bits index the byte.
		bits[i] = ((bytes[i >> 3] >> (i & 7)) & 1u8) as i8;
	}
	bits
}

pub fn get_bits_at(scalar: &Scalar, process_bits: usize) -> Vec<u8> {
	let mut bits = vec![0u8; process_bits];
	let bytes = scalar.as_bytes();
	for i in 0..process_bits {
		// As i runs from 0..256, the bottom 3 bits index the bit,
		// while the upper bits index the byte.
		bits[i] = ((bytes[i >> 3] >> (i & 7)) & 1u8) as u8;
	}
	bits
}

pub fn scalar_to_u64_array(scalar: &Scalar) -> [u64; 4] {
	use byteorder::{ByteOrder, LittleEndian};
	let bytes = scalar.to_bytes();
	let mut result = [0; 4];
	LittleEndian::read_u64_into(&bytes, &mut result);
	result
}

pub fn u64_array_to_scalar(array: &[u64; 4]) -> Scalar {
	use byteorder::{ByteOrder, LittleEndian};
	let mut result: [u8; 32] = [0; 32];
	LittleEndian::write_u64_into(array, &mut result);
	let s = Scalar::from_bits(result);
	s.reduce()
}

pub fn decode_hex(s: &str) -> Result<Vec<u8>, DecodeHexError> {
	let s = if s[0..2] == *"0x" || s[0..2] == *"0X" {
		match s.char_indices().skip(2).next() {
			Some((pos, _)) => &s[pos..],
			None => "",
		}
	} else {
		s
	};
	if s.len() % 2 != 0 {
		Err(DecodeHexError::OddLength)
	} else {
		(0..s.len())
			.step_by(2)
			.map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.into()))
			.collect()
	}
}
impl From<ParseIntError> for DecodeHexError {
	fn from(e: ParseIntError) -> Self {
		DecodeHexError::ParseInt(e)
	}
}

pub fn get_scalar_from_hex(hex_str: &str) -> Result<Scalar, DecodeHexError> {
	let bytes = decode_hex(hex_str)?;
	let mut result: [u8; 32] = [0; 32];
	result.copy_from_slice(&bytes);
	Ok(Scalar::from_bytes_mod_order(result))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeHexError {
	OddLength,
	ParseInt(ParseIntError),
}
