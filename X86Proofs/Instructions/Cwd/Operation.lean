import X86Proofs.Core.Gpr
import X86Proofs.Core.Operand

/-!
# CWD, CDQ, CQO specification

`CWD` (`66 99`): `DX:AX ← SignExtend(AX)`; `CDQ` (`99`): `EDX:EAX ← SignExtend(EAX)`; `CQO`
(`REX.W 99`): `RDX:RAX ← SignExtend(RAX)` (Intel SDM; lean-x86's `Operations.SIGNEXTEND2 n`). The
accumulator at the operand size `n` is unchanged; the data register gets the upper half of its
`2n`-bit sign extension, every bit a copy of the accumulator's sign bit. No flags are affected.
`cwdSpec x` is that upper half.
-/

namespace X86Proofs

/-- The value CWD, CDQ or CQO writes to DX, EDX or RDX: all ones if the sign bit of the accumulator
`x` is set, zero otherwise. No flags, no oracle bits. -/
def cwdSpec {n : Nat} (x : BitVec n) : BitVec n := if x.msb then BitVec.allOnes n else 0

open X86 X86.Helpers

theorem extractLsb'_signExtend_high {n m : Nat} (x : BitVec n) (hm : n + n ≤ m) :
    (x.signExtend m).extractLsb' n n = cwdSpec x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_signExtend, cwdSpec, show n + i < m by omega, show ¬ n + i < n by omega,
    ite_false]
  cases x.msb <;> simp [hi]

theorem cwd_operation {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (n : Nat)
    (hn : n = 16 ∨ n = 32 ∨ n = 64) :
    (X86.Instructions.Operations.SIGNEXTEND2 n : Runtime.SpecM Exception (X86.State σ) Unit).run
        s =
      (.ok (), (Operand.reg 2 : Operand n).write s
        (cwdSpec ((Operand.reg 0 : Operand n).read s))) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SIGNEXTEND2
    simp only [x86_runtime, pure_bind, bind_assoc]
    spec_bind_rfl
    spec_bind_with rax_run _
    rw [stdSignExtend_eq_pure _ (by decide) (by decide)]
    spec_bind_rfl
    rw [writeRDX_run _ _ (by decide), Operand.write_reg_eq_set]
    simp only [Int.reduceToNat]
    rw [extractLsb'_signExtend_high _ (by decide)]
    simp (disch := decide) only [Operand.read, extractLsb'_zero_eq_setWidth]
