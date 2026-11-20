import X86Proofs.Core.Float

/-!
# LDMXCSR specification

`LDMXCSR m32` (`NP 0F AE /2`) loads MXCSR from memory: `MXCSR ← m32`. A value with any of the
reserved bits 16–31 set raises #GP(0) (`Check_MXCSR_Reserved_Bits`); the triples exclude it by
their precondition (`LdmxcsrPre`), so the operation is the load itself. lean-x86 computes it with
`Operations.LDMXCSR`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The MXCSR value LDMXCSR loads: the doubleword itself. -/
def ldmxcsrSpec (v : BitVec 32) : BitVec 32 := v

theorem ldmxcsr_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (v : BitVec 32)
    (hres : v.extractLsb' 16 16 = 0) :
    (X86.Instructions.Operations.LDMXCSR v).run s =
      (.ok (), { s with MXCSR := ldmxcsrSpec v }) := by
  unfold X86.Instructions.Operations.LDMXCSR Check_MXCSR_Reserved_Bits
  simp only [MXCSR_Type.RESERVED, x86_runtime, stdIsZero_eq_ok, hres]
  rfl

end X86Proofs
