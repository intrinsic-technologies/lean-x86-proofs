import X86Proofs.Core.Gpr
import X86Proofs.Core.Operand

/-!
# CBW, CWDE, CDQE specification

`CBW` (`66 98`): `AX ← SignExtend(AL)`; `CWDE` (`98`): `EAX ← SignExtend(AX)`; `CDQE`
(`REX.W 98`): `RAX ← SignExtend(EAX)`. The low half of the accumulator, at the operand size
`n`, is sign-extended to `n` bits (Intel SDM; lean-x86's `Operations.SIGNEXTEND1 n`). No flags
are affected. `cbwSpec n x` is the result, `x.signExtend n`.
-/

namespace X86Proofs

/-- The result of CBW, CWDE or CDQE at operand size `n`: the half-size source `x` sign-extended to
`n` bits. No flags, no oracle bits. -/
def cbwSpec {m : Nat} (n : Nat) (x : BitVec m) : BitVec n := x.signExtend n

open X86 X86.Helpers

theorem cbw_operation {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (n : Nat)
    (hn : n = 16 ∨ n = 32 ∨ n = 64) :
    (X86.Instructions.Operations.SIGNEXTEND1 n : Runtime.SpecM Exception (X86.State σ) Unit).run
        s =
      (.ok (), (Operand.reg 0 : Operand n).write s
        (cbwSpec n ((Operand.reg 0 : Operand (n / 2)).read s))) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SIGNEXTEND1
    simp only [x86_runtime, pure_bind, Int.reduceDiv, bind_assoc]
    spec_bind_rfl
    spec_bind_with rax_run _
    rw [stdSignExtend_eq_pure _ (by decide) (by decide)]
    spec_bind_rfl
    rw [writeRAX_run _ _ (by decide), Operand.write_reg_eq_set]
    simp (disch := decide) only [cbwSpec, Operand.read, extractLsb'_zero_eq_setWidth]
    rfl
