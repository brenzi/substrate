// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use primitives::hashing::{
	blake2_128, blake2_256, twox_128, twox_256, twox_64
};

#[macro_use]
use std::fmt;
#[macro_use]
use std::vec::Vec;


/*
#[doc(hidden)]
pub use rstd;
pub use rstd::{mem, slice};

use rstd::prelude::*;

use core::{intrinsics, panic::PanicInfo};
use rstd::{vec::Vec, cell::Cell};
*/

//use primitives::{ed25519, Blake2Hasher, sr25519 };

/*
// Switch to this after PoC-3
// pub use primitives::BlakeHasher;
pub use substrate_state_machine::{
	Externalities,
	BasicExternalities,
	TestExternalities,
	ChildStorageKey
};
*/
//use primitives::H256;

use environmental::environmental;

use std::collections::HashMap;

pub type SgxExternalities = HashMap<Vec<u8>, Vec<u8>>;

environmental!(hm: SgxExternalities);

/*use twox_hash;

use std::hash::BuildHasherDefault;
use std::collections::HashMap;
use twox_hash::XxHash;

let mut my_store: HashMap<_, _, BuildHasherDefault<XxHash>> = Default::default();
*/

/// Additional bounds for `Hasher` trait for with_std.
pub trait HasherBounds {}
impl<T: Hasher> HasherBounds for T {}


/*
/// Ensures we use the right crypto when calling into native
pub trait ExternTrieCrypto: Hasher {
	/// Calculate enumerated trie root.
	fn enumerated_trie_root(values: &[&[u8]]) -> Self::Out;
}

/// Additional bounds for Hasher trait for without_std.
pub trait HasherBounds: ExternTrieCrypto {}
impl<T: ExternTrieCrypto + Hasher> HasherBounds for T {}
*/

/*
// Ensures we use a Blake2_256-flavored Hasher when calling into native
impl ExternTrieCrypto for Blake2Hasher {
	fn enumerated_trie_root(values: &[&[u8]]) -> Self::Out {
		let lengths = values.iter().map(|v| (v.len() as u32).to_le()).collect::<Vec<_>>();
		let values = values.iter().fold(Vec::new(), |mut acc, sl| { acc.extend_from_slice(sl); acc });
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_blake2_256_enumerated_trie_root.get()(
				values.as_ptr(),
				lengths.as_ptr(),
				lengths.len() as u32,
				result.as_mut_ptr()
			);
		}
		result.into()
	}
}
*/

/*
/// Returns a `ChildStorageKey` if the given `storage_key` slice is a valid storage
/// key or panics otherwise.
///
/// Panicking here is aligned with what the `without_std` environment would do
/// in the case of an invalid child storage key.
fn child_storage_key_or_panic(storage_key: &[u8]) -> ChildStorageKey<Blake2Hasher> {

	match ChildStorageKey::from_slice(storage_key) {
		Some(storage_key) => storage_key,
		None => panic!("child storage key is invalid"),
	}
}
*/
impl StorageApi for () {
	fn storage(key: &[u8]) -> Option<Vec<u8>> {
		#[cfg(feature = "debug")] println!("storage('{:?}')", key);
		//hm::with(|hm| println!("key exists?: {:?}", hm.contains_key(key)));
		hm::with(|hm| hm.get(key).map(|s| {
			#[cfg(feature = "debug")] println!("  returning {:?}", s);
			s.to_vec()
		}))
			.expect("storage cannot be called outside of an Externalities-provided environment.")
	}

	fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
		#[cfg(feature = "debug")]
		println!("read_storage('{:?}' with offset =  {:?}. value_out.len() is {})", key, value_offset, value_out.len());
		hm::with(|hm| hm.get(key).map(|value| {
			#[cfg(feature = "debug")] println!("  entire stored value: {:?}", value);
			let value = &value[value_offset..];
			#[cfg(feature = "debug")] println!("  stored value at offset: {:?}", value);
			let written = std::cmp::min(value.len(), value_out.len());
			value_out[..written].copy_from_slice(&value[..written]);
			#[cfg(feature = "debug")] println!("  write back {:?}, return len {}", value_out, value.len());
			value.len()
		})).expect("read_storage cannot be called outside of an Externalities-provided environment.")
	}

	fn child_storage(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		println!("StorageApi::child_storage() unimplemented");
		Some(vec![0,1,2,3])
	}

	fn set_storage(key: &[u8], value: &[u8]) {
		#[cfg(feature = "debug")] println!("set_storage('{:?}', {:x?})", key, value);
		hm::with(|hm|
			hm.insert(key.to_vec(), value.to_vec())
		);
	}

	fn read_child_storage(
		storage_key: &[u8],
		key: &[u8],
		value_out: &mut [u8],
		value_offset: usize,
	) -> Option<usize> {
		println!("StorageApi::read_child_storage() unimplemented");
		Some(0)
	}

	fn set_child_storage(storage_key: &[u8], key: &[u8], value: &[u8]) {
		println!("StorageApi::set_child_storage() unimplemented");
	}

	fn clear_storage(key: &[u8]) {
		println!("StorageApi::clear_storage() unimplemented");
	}

	fn clear_child_storage(storage_key: &[u8], key: &[u8]) {
		println!("StorageApi::clear_child_storage() unimplemented");
	}

	fn kill_child_storage(storage_key: &[u8]) {
		println!("StorageApi::kill_child_storage() unimplemented");
	}

	fn exists_storage(key: &[u8]) -> bool {
		println!("StorageApi::exists_storage() unimplemented");
		false
	}

	fn exists_child_storage(storage_key: &[u8], key: &[u8]) -> bool {
		println!("StorageApi::exists_child_storage() unimplemented");
		false
	}

	fn clear_prefix(prefix: &[u8]) {
		println!("StorageApi::clear_storage() unimplemented");
	}

	fn storage_root() -> [u8; 32] {
		println!("StorageApi::storage_root() unimplemented");
		[0u8; 32]
	}

	fn child_storage_root(storage_key: &[u8]) -> Vec<u8> {
		println!("StorageApi::child_storage_root() unimplemented");
		vec![0,1,2,3]
	}

	fn storage_changes_root(parent_hash: [u8; 32], parent_num: u64) -> Option<[u8; 32]> {
		println!("StorageApi::storage_changes_root() unimplemented");
		Some([0u8; 32])
	}

	fn enumerated_trie_root<H>(input: &[&[u8]]) -> H::Out
	where
		H: Hasher,
		H::Out: Ord,
	{
		//trie::ordered_trie_root::<H, _, _>(input.iter())
		println!("StorageApi::enumerate_trie_root() unimplemented");
		H::Out::default()
	}

	fn trie_root<H, I, A, B>(input: I) -> H::Out
	where
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
		H: Hasher,
		H::Out: Ord,
	{
		//trie::trie_root::<H, _, _, _>(input)
		println!("StorageApi::trie_root() unimplemented");
		H::Out::default()
	}

	fn ordered_trie_root<H, I, A>(input: I) -> H::Out
	where
		I: IntoIterator<Item = A>,
		A: AsRef<[u8]>,
		H: Hasher,
		H::Out: Ord,
	{
		//trie::ordered_trie_root::<H, _, _>(input)
		println!("StorageApi::ordered_trie_root() unimplemented");
		H::Out::default()
	}
}

impl OtherApi for () {
	fn chain_id() -> u64 {
		println!("OtherApi::chain_id unimplemented");
		0
	}

	fn print<T: Printable + Sized>(value: T) {
		value.print()
	}
}

impl CryptoApi for () {
	fn ed25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
		println!("CryptoApi::ed25519_verify unimplemented");
		true
		//ed25519::Pair::verify_weak(sig, msg, pubkey)
	}

	fn sr25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
		println!("CryptoApi::sr25519_verify unimplemented");
		true
		//sr25519::Pair::verify_weak(sig, msg, pubkey)
	}

	fn secp256k1_ecdsa_recover(sig: &[u8; 65], msg: &[u8; 32]) -> Result<[u8; 64], EcdsaVerifyError> {
		println!("CryptoApi::secp256k1_ecdsa_recover unimplemented");
		Err(EcdsaVerifyError::BadRS)
/*
		let rs = secp256k1::Signature::parse_slice(&sig[0..64]).map_err(|_| EcdsaVerifyError::BadRS)?;
		let v = secp256k1::RecoveryId::parse(if sig[64] > 26 { sig[64] - 27 } else { sig[64] } as u8).map_err(|_| EcdsaVerifyError::BadV)?;
		let pubkey = secp256k1::recover(&secp256k1::Message::parse(msg), &rs, &v).map_err(|_| EcdsaVerifyError::BadSignature)?;
		let mut res = [0u8; 64];
		res.copy_from_slice(&pubkey.serialize()[1..65]);
		Ok(res)
		*/
	}
}




impl HashingApi for () {
	fn keccak_256(data: &[u8]) -> [u8; 32] {
		println!("HashingApi::keccak256 unimplemented");
		[0u8; 32]
		//tiny_keccak::keccak256(data)
	}

	fn blake2_128(data: &[u8]) -> [u8; 16] {
		#[cfg(feature = "debug")] println!("blake2_128 of {:x?}", data);
		let hash = blake2_128(data);
		#[cfg(feature = "debug")] println!("  returning {:?}", hash);
		hash
	}

	fn blake2_256(data: &[u8]) -> [u8; 32] {
		#[cfg(feature = "debug")] println!("blake2_256 of {:x?}", data);
		let hash = blake2_256(data);
		#[cfg(feature = "debug")] println!("  returning {:?}", hash);
		hash
	}

	fn twox_256(data: &[u8]) -> [u8; 32] {
		#[cfg(feature = "debug")] println!("twox_256 of {:x?}", data);
		let hash = twox_256(data);
		#[cfg(feature = "debug")] println!("  returning {:?}", hash);
		hash
	}

	fn twox_128(data: &[u8]) -> [u8; 16] {
		#[cfg(feature = "debug")] println!("twox_128 of {:x?}", data);
		let hash = twox_128(data);
		#[cfg(feature = "debug")] println!("  returning {:?}", hash);
		hash
	}

	fn twox_64(data: &[u8]) -> [u8; 8] {
		#[cfg(feature = "debug")] println!("twox_64 of {:x?}", data);
		let hash = twox_64(data);
		#[cfg(feature = "debug")] println!("  returning {:?}", hash);
		hash
	}
}

impl OffchainApi for () {
	fn submit_extrinsic<T: codec::Encode>(data: &T) {
		println!("OffchainApi::submit_extrinsic unimplemented");
	}
}

impl Api for () {}


/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
// NOTE: need a concrete hasher here due to limitations of the `environmental!` macro, otherwise a type param would have been fine I think.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut SgxExternalities, f: F) -> R {
	hm::using(ext, f)
}


/// A set of key value pairs for storage.
pub type StorageOverlay = (); //HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
pub type ChildrenStorageOverlay = (); //HashMap<Vec<u8>, StorageOverlay>;

/*
/// Execute the given closure with global functions available whose functionality routes into
/// externalities that draw from and populate `storage`. Forwards the value that the closure returns.
pub fn with_storage<R, F: FnOnce() -> R>(storage: &mut StorageOverlay, f: F) -> R {
	let mut alt_storage = Default::default();
	rstd::mem::swap(&mut alt_storage, storage);
	let mut ext: BasicExternalities = alt_storage.into();
	let r = ext::using(&mut ext, f);
	*storage = ext.into();
	r
}
*/

impl<'a> Printable for &'a [u8] {
	fn print(self) {
		println!("Runtime: {:?}", &self);
	}
}

impl<'a> Printable for &'a str {
	fn print(self) {
		println!("Runtime: {}", self);
	}
}

impl Printable for u64 {
	fn print(self) {
		println!("Runtime: {}", self);
	}
}

#[cfg(test)]
mod std_tests {
	use super::*;
//	use primitives::map;

	#[test]
	fn storage_works() {
		let mut t = SgxExternalities::default();
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), Some(b"world".to_vec()));
			assert_eq!(storage(b"foo"), None);
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t = SgxExternalities::new();
		t.insert(b"foo".to_vec(), b"bar".to_vec());

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			assert_eq!(storage(b"foo"), Some(b"bar".to_vec()));
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t = SgxExternalities::new();
/*			map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		]);*/
		
		with_externalities(&mut t, || {
			set_storage(b"test", b"\x0b\0\0\0Hello world");
			let mut v = [0u8; 4];
			assert!(read_storage(b":test", &mut v[..], 0).unwrap() >= 4);
			assert_eq!(v, [11u8, 0, 0, 0]);
			let mut w = [0u8; 11];
			assert!(read_storage(b":test", &mut w[..], 4).unwrap() >= 11);
			assert_eq!(&w, b"Hello world");
		});
	}

	#[test]
	fn clear_prefix_works() {
		let mut t = SgxExternalities::new();
		
/*		map![
			b":a".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abcd".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abc".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abdd".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		]);
		*/

		with_externalities(&mut t, || {
			clear_prefix(b":abc");

			assert!(storage(b":a").is_some());
			assert!(storage(b":abdd").is_some());
			assert!(storage(b":abcd").is_none());
			assert!(storage(b":abc").is_none());
		});
	}
}
