import X86Proofs.Core.Operand
import X86Proofs.Program.ComposeAttr

/-!
# CLD specification

`CLD` (`FC`): `DF ← 0`. The other flags in RFLAGS are unaffected (Intel SDM). `cldSpec` is
the value DF has after it.
-/

namespace X86Proofs

/-- The direction flag after CLD: clear. -/
def cldSpec : BitVec 1 := 0#1

open X86 X86.Machine

theorem cld_operation {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (X86.Instructions.Operations.CLD : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), (Operand.df : Operand 1).write s cldSpec) := by
  unfold X86.Instructions.Operations.CLD
  rw [rflagsSetDF_run, Operand.write_df]
  rfl

attribute [x86_compose] cldSpec

end X86Proofs
