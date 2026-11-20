import Lean

/-!
# The `x86_runtime` simp set

Declared here, apart from `X86Proofs.Core.Runtime` which fills it, because an attribute cannot be
used in the module that declares it.
-/

/-- Lemmas about lean-x86's runtime helpers (`X86.Runtime.*`, `X86.Helpers.Std.Bits.*`), stated in
plain `BitVec`, `Int`, `Nat` and `List` terms. Filled by `X86Proofs.Core.Runtime`. -/
register_simp_attr x86_runtime
