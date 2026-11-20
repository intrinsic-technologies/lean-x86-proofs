import X86Proofs.Core.Float

/-!
# STMXCSR specification

`STMXCSR m32` (`NP 0F AE /3`) stores MXCSR to memory: `m32 ← MXCSR`, the reserved bits 16–31
stored as zero (lean-x86's `Operations.STMXCSR` clears them; a valid MXCSR has them clear anyway).
`stmxcsrSpec mx` is the doubleword stored.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The doubleword STMXCSR stores: MXCSR's low 16 bits, zero-extended. -/
def stmxcsrSpec (mx : BitVec 32) : BitVec 32 := (mx.setWidth 16).setWidth 32

theorem stmxcsr_operation (s : X86.Machine.RamState) :
    (X86.Instructions.Operations.STMXCSR : X86.Runtime.SpecM _ X86.Machine.RamState _).run s =
      (.ok (stmxcsrSpec s.MXCSR), s) := by
  unfold X86.Instructions.Operations.STMXCSR
  simp only [x86_runtime, MXCSR_Type.setRESERVED]
  show (Except.ok (X86.Runtime.setSlice s.MXCSR 16 16 0), s) = _
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_setSlice _ _ _ _ _ hi]
  unfold stmxcsrSpec
  have hi' : i < 32 := by simpa using hi
  by_cases h : i < 16
  · simp [h, hi', show ¬ 16 ≤ i by omega]
  · simp [h]
    omega

end X86Proofs
