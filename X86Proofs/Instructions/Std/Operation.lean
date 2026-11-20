import X86Proofs.Core.Operand
import X86Proofs.Program.ComposeAttr

/-!
# STD specification

`STD` (`FD`): `DF ← 1`. The other flags in RFLAGS are unaffected (Intel SDM). `stdSpec` is
the value DF has after it.
-/

namespace X86Proofs

/-- The direction flag after STD: set. -/
def stdSpec : BitVec 1 := 1#1

open X86 X86.Machine

theorem std_operation {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (X86.Instructions.Operations.STD : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), (Operand.df : Operand 1).write s stdSpec) := by
  unfold X86.Instructions.Operations.STD
  rw [rflagsSetDF_run, Operand.write_df]
  rfl

attribute [x86_compose] stdSpec

end X86Proofs
