import X86Proofs.Core.Fpu

/-!
# EMMS specification

`EMMS` (`NP 0F 77`): empty the MMX state, `x87FPUTagWord ← FFFFH`: every physical x87 register is
tagged empty, so the next x87 instruction can use the register stack again. lean-x86's
`Operations.EMMS` also sets the stack top TOP to 0 (`mmxStatus`), as every MMX instruction does.
`emmsSpec` is the tag word it leaves. No flags.
-/

namespace X86Proofs

/-- The tag word after EMMS: all ones, `11` (empty) for each of the eight registers. -/
def emmsSpec : BitVec 16 := 0xFFFF

open X86

theorem emms_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.EMMS : X86.Runtime.SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Tag_Word := emmsSpec, FP87_Status := mmxStatus s.FP87_Status }) := by
  unfold X86.Instructions.Operations.EMMS
  spec_run [
    X86.FP87_Tag_Word.assign => fp87TagWordAssign_run _ _,
    X86.FP87_Status.setTOP => fp87StatusSetTOP_run _]

end X86Proofs
