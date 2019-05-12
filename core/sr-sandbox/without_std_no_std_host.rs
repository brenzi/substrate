// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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


use rstd::prelude::*;
use rstd::{slice, marker, mem};
use rstd::rc::Rc;
use rstd::vec::Vec;
use codec::{Decode, Encode};
use primitives::sandbox as sandbox_primitives;


use rstd::collections::btree_map::BTreeMap;
//use rstd::fmt;

/*
use wasmi::{
	Externals, FuncInstance, FuncRef, GlobalDescriptor, GlobalRef, ImportResolver,
	MemoryDescriptor, MemoryInstance, MemoryRef, Module, ModuleInstance, ModuleRef,
	RuntimeArgs, RuntimeValue, Signature, TableDescriptor, TableRef, Trap, TrapKind
};
use wasmi::memory_units::Pages;
*/

use super::{Error, TypedValue, ReturnValue, HostFuncType};

#[derive(Clone)]
pub struct Memory {
}

impl Memory {
	pub fn new(initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
		//print("sr-sandbox::Memory::new unimplemented");
		Ok(Memory{ })
	}

	pub fn get(&self, ptr: u32, buf: &mut [u8]) -> Result<(), Error> {
		//print("sr-sandbox::Memory::get unimplemented");
		Ok(())
	}

	pub fn set(&self, ptr: u32, value: &[u8]) -> Result<(), Error> {
		//print("sr-sandbox::Memory::set unimplemented");
		Ok(())
	}
}

struct HostFuncIndex(usize);

struct DefinedHostFunctions<T> {
	funcs: Vec<HostFuncType<T>>,
}

impl<T> Clone for DefinedHostFunctions<T> {
	fn clone(&self) -> DefinedHostFunctions<T> {
		DefinedHostFunctions {
			funcs: self.funcs.clone(),
		}
	}
}

impl<T> DefinedHostFunctions<T> {
	fn new() -> DefinedHostFunctions<T> {
		DefinedHostFunctions {
			funcs: Vec::new(),
		}
	}

	fn define(&mut self, f: HostFuncType<T>) -> HostFuncIndex {
		let idx = self.funcs.len();
		self.funcs.push(f);
		HostFuncIndex(idx)
	}
}
/*
#[derive(Debug)]
struct DummyHostError;

impl fmt::Display for DummyHostError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "DummyHostError")
	}
}

impl wasmi::HostError for DummyHostError {
}
*/

/*
struct GuestExternals<'a, T: 'a> {
	state: &'a mut T,
	defined_host_functions: &'a DefinedHostFunctions<T>,
}

impl<'a, T> Externals for GuestExternals<'a, T> {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> Result<Option<RuntimeValue>, Trap> {
		let args = args.as_ref()
			.iter()
			.cloned()
			.map(from_runtime_value)
			.collect::<Vec<_>>();

		let result = (self.defined_host_functions.funcs[index])(self.state, &args);
		match result {
			Ok(value) => Ok(match value {
				ReturnValue::Value(v) => Some(to_runtime_value(v)),
				ReturnValue::Unit => None,
			}),
			Err(_) => Err(()).into(),
		}
	}
}
*/
enum ExternVal {
	HostFunc(HostFuncIndex),
	Memory(Memory),
}

pub struct EnvironmentDefinitionBuilder<T> {
	map: BTreeMap<(Vec<u8>, Vec<u8>), ExternVal>,
	defined_host_functions: DefinedHostFunctions<T>,
}

impl<T> EnvironmentDefinitionBuilder<T> {
	pub fn new() -> EnvironmentDefinitionBuilder<T> {
		EnvironmentDefinitionBuilder {
			map: BTreeMap::new(),
			defined_host_functions: DefinedHostFunctions::new(),
		}
	}

	pub fn add_host_func<N1, N2>(&mut self, module: N1, field: N2, f: HostFuncType<T>)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		let idx = self.defined_host_functions.define(f);
		self.map
			.insert((module.into(), field.into()), ExternVal::HostFunc(idx));
	}

	pub fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		self.map
			.insert((module.into(), field.into()), ExternVal::Memory(mem));
	}
}

/*
impl<T> ImportResolver for EnvironmentDefinitionBuilder<T> {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &Signature,
	) -> Result<FuncRef, Error> {
		let key = (
			module_name.as_bytes().to_owned(),
			field_name.as_bytes().to_owned(),
		);
		let externval = self.map.get(&key).ok_or_else(|| {
			Error::default()
		})?;
		let host_func_idx = match *externval {
			ExternVal::HostFunc(ref idx) => idx,
			_ => {
				return Err(Error::default())
			}
		};
		Ok(())
	}

	fn resolve_global(
		&self,
		_module_name: &str,
		_field_name: &str,
		_global_type: &GlobalDescriptor,
	) -> Result<GlobalRef, Error> {
		Err(Error::default())
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &MemoryDescriptor,
	) -> Result<MemoryRef, Error> {
		let key = (
			module_name.as_bytes().to_owned(),
			field_name.as_bytes().to_owned(),
		);
		let externval = self.map.get(&key).ok_or_else(|| {
			Error::default()
		})?;
		let memory = match *externval {
			ExternVal::Memory(ref m) => m,
			_ => {
				return Err(Error::default())
			}
		};
		Ok(memory.memref.clone())
	}

	fn resolve_table(
		&self,
		_module_name: &str,
		_field_name: &str,
		_table_type: &TableDescriptor,
	) -> Result<TableRef, Error> {
		Err(Error::default())
	}
}
*/

#[derive(Default)]
pub struct Instance<T> {
	_marker: ::core::marker::PhantomData<T>,
}

impl<T> Instance<T> {
	pub fn new(code: &[u8], env_def_builder: &EnvironmentDefinitionBuilder<T>, state: &mut T) -> Result<Instance<T>, Error> {
		//print("sr_sandbox::Instance::new unimplemented");
		Ok(Instance {
			_marker: ::core::marker::PhantomData::<T>,
		})
	}

	pub fn invoke(
		&mut self,
		name: &[u8],
		args: &[TypedValue],
		state: &mut T,
	) -> Result<ReturnValue, Error> {
		let mut return_val = vec![0u8; sandbox_primitives::ReturnValue::ENCODED_MAX_SIZE];
		let return_val = sandbox_primitives::ReturnValue::decode(&mut &return_val[..]).unwrap();
		//print("sr_sandbox::Instance::invoke unimplemented");
		Ok(return_val)
	}
}

#[cfg(test)]
mod tests {
	use wabt;
	use crate::{Error, TypedValue, ReturnValue, HostError, EnvironmentDefinitionBuilder, Instance};
	use assert_matches::assert_matches;

	fn execute_sandboxed(code: &[u8], args: &[TypedValue]) -> Result<ReturnValue, HostError> {
		struct State {
			counter: u32,
		}

		fn env_assert(_e: &mut State, args: &[TypedValue]) -> Result<ReturnValue, HostError> {
			if args.len() != 1 {
				return Err(HostError);
			}
			let condition = args[0].as_i32().ok_or_else(|| HostError)?;
			if condition != 0 {
				Ok(ReturnValue::Unit)
			} else {
				Err(HostError)
			}
		}
		fn env_inc_counter(e: &mut State, args: &[TypedValue]) -> Result<ReturnValue, HostError> {
			if args.len() != 1 {
				return Err(HostError);
			}
			let inc_by = args[0].as_i32().ok_or_else(|| HostError)?;
			e.counter += inc_by as u32;
			Ok(ReturnValue::Value(TypedValue::I32(e.counter as i32)))
		}
		/// Function that takes one argument of any type and returns that value.
		fn env_polymorphic_id(_e: &mut State, args: &[TypedValue]) -> Result<ReturnValue, HostError> {
			if args.len() != 1 {
				return Err(HostError);
			}
			Ok(ReturnValue::Value(args[0]))
		}

		let mut state = State { counter: 0 };

		let mut env_builder = EnvironmentDefinitionBuilder::new();
		env_builder.add_host_func("env", "assert", env_assert);
		env_builder.add_host_func("env", "inc_counter", env_inc_counter);
		env_builder.add_host_func("env", "polymorphic_id", env_polymorphic_id);

		let mut instance = Instance::new(code, &env_builder, &mut state)?;
		let result = instance.invoke(b"call", args, &mut state);

		result.map_err(|_| HostError)
	}

	#[test]
	fn invoke_args() {
		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "assert" (func $assert (param i32)))

			(func (export "call") (param $x i32) (param $y i64)
				;; assert that $x = 0x12345678
				(call $assert
					(i32.eq
						(get_local $x)
						(i32.const 0x12345678)
					)
				)

				(call $assert
					(i64.eq
						(get_local $y)
						(i64.const 0x1234567887654321)
					)
				)
			)
		)
		"#).unwrap();

		let result = execute_sandboxed(
			&code,
			&[
				TypedValue::I32(0x12345678),
				TypedValue::I64(0x1234567887654321),
			]
		);
		assert!(result.is_ok());
	}

	#[test]
	fn return_value() {
		let code = wabt::wat2wasm(r#"
		(module
			(func (export "call") (param $x i32) (result i32)
				(i32.add
					(get_local $x)
					(i32.const 1)
				)
			)
		)
		"#).unwrap();

		let return_val = execute_sandboxed(
			&code,
			&[
				TypedValue::I32(0x1336),
			]
		).unwrap();
		assert_eq!(return_val, ReturnValue::Value(TypedValue::I32(0x1337)));
	}

	#[test]
	fn signatures_dont_matter() {
		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "polymorphic_id" (func $id_i32 (param i32) (result i32)))
			(import "env" "polymorphic_id" (func $id_i64 (param i64) (result i64)))
			(import "env" "assert" (func $assert (param i32)))

			(func (export "call")
				;; assert that we can actually call the "same" function with different
				;; signatures.
				(call $assert
					(i32.eq
						(call $id_i32
							(i32.const 0x012345678)
						)
						(i32.const 0x012345678)
					)
				)
				(call $assert
					(i64.eq
						(call $id_i64
							(i64.const 0x0123456789abcdef)
						)
						(i64.const 0x0123456789abcdef)
					)
				)
			)
		)
		"#).unwrap();

		let return_val = execute_sandboxed(&code, &[]).unwrap();
		assert_eq!(return_val, ReturnValue::Unit);
	}

	#[test]
	fn cant_return_unmatching_type() {
		fn env_returns_i32(_e: &mut (), _args: &[TypedValue]) -> Result<ReturnValue, HostError> {
			Ok(ReturnValue::Value(TypedValue::I32(42)))
		}

		let mut env_builder = EnvironmentDefinitionBuilder::new();
		env_builder.add_host_func("env", "returns_i32", env_returns_i32);

		let code = wabt::wat2wasm(r#"
		(module
			;; It's actually returns i32, but imported as if it returned i64
			(import "env" "returns_i32" (func $returns_i32 (result i64)))

			(func (export "call")
				(drop
					(call $returns_i32)
				)
			)
		)
		"#).unwrap();

		// It succeeds since we are able to import functions with types we want.
		let mut instance = Instance::new(&code, &env_builder, &mut ()).unwrap();

		// But this fails since we imported a function that returns i32 as if it returned i64.
		assert_matches!(
			instance.invoke(b"call", &[], &mut ()),
			Err(Error::Execution)
		);
	}
}
