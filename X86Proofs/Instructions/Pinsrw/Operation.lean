import X86Proofs.Core.Lanes
import X86Proofs.Core.Run

/-!
# PINSRW specification

`PINSRW xmm, r32/m16, imm8` (`66 0F C4 /r ib`): replace the word of the destination the low three
bits of the immediate select with the low word of the source, `SEL ← imm8[2:0]; MASK ← FFFFH <<
(SEL * 16); DEST ← (DEST AND NOT MASK) OR ((SRC << (SEL * 16)) AND MASK)`. `pinsrwSpec` is the
result; lean-x86 computes it with `Operations.PINSR 16 128 n` (`n` the source's size), a
`PartialResult` (its selector width comes from `Std.Integer.Log2`). No flags.

The MMX forms (`NP 0F C4`) insert into one of the four words of an MMX register: `pinsrwMmxSpec`
(`Operations.PINSR 16 64`).
-/

namespace X86Proofs

/-- Word `imm[2:0]` of the result is the low word of `x`; the other words are `a`'s. -/
def pinsrwSpec {n : Nat} (a : BitVec 128) (x : BitVec n) (imm : BitVec 8) : BitVec 128 :=
  ofLanes 128 16 fun i =>
    if i = (imm.extractLsb' 0 3).toNat then x.extractLsb' 0 16 else lane 16 a i

/-- The MMX forms (`PINSRW mm, r32/m16, imm8`, `NP 0F C4`): word `imm[1:0]` of the result is the
low word of `x`; the other three words are `a`'s. -/
def pinsrwMmxSpec {n : Nat} (a : BitVec 64) (x : BitVec n) (imm : BitVec 8) : BitVec 64 :=
  ofLanes 64 16 fun i =>
    if i = (imm.extractLsb' 0 2).toNat then x.extractLsb' 0 16 else lane 16 a i

open X86

theorem pinsrw_operation (n : Nat) (hn : n = 16 ∨ n = 32) (a : BitVec 128) (x : BitVec n)
    (imm : BitVec 8) :
    X86.Instructions.Operations.PINSR 16 128 n a x imm =
      (pure (pinsrwSpec a x imm) : X86.Runtime.PartialResult Empty (BitVec 128)) := by
  rcases hn with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PINSR
    simp only [x86_runtime, pure_bind, Int.reduceDiv, stdLog2_eight]
    have hv := (imm.extractLsb' 0 3).isLt
    simp only [Nat.reducePow] at hv
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, bind_pure]
    rw [show (((imm.extractLsb' 0 3).toNat : Int) * 16).toNat = (imm.extractLsb' 0 3).toNat * 16 by
      omega]
    refine congrArg pure (BitVec.eq_of_getLsbD_eq fun k hk => ?_)
    rw [getLsbD_setSlice _ _ _ _ _ hk, pinsrwSpec, getLsbD_ofLanes _ _ hk]
    rw [ite_eq_left (show k < 128 / 16 * 16 by omega)]
    generalize (imm.extractLsb' 0 3).toNat = j at *
    by_cases hin : j * 16 ≤ k ∧ k < j * 16 + 16
    · rw [ite_eq_left hin, ite_eq_left (show k / 16 = j by omega),
        show k - j * 16 = k % 16 by omega]
    · rw [ite_eq_right hin, ite_eq_right (show ¬ k / 16 = j by omega)]
      simp only [lane, BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 16),
        decide_true, Bool.true_and]
      rw [Nat.mul_comm, Nat.div_add_mod]

theorem pinsrw_mmx_operation (n : Nat) (hn : n = 16 ∨ n = 32) (a : BitVec 64) (x : BitVec n)
    (imm : BitVec 8) :
    X86.Instructions.Operations.PINSR 16 64 n a x imm =
      (pure (pinsrwMmxSpec a x imm) : X86.Runtime.PartialResult Empty (BitVec 64)) := by
  rcases hn with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PINSR
    simp only [x86_runtime, pure_bind, Int.reduceDiv, stdLog2_four]
    have hv := (imm.extractLsb' 0 2).isLt
    simp only [Nat.reducePow] at hv
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, bind_pure]
    rw [show (((imm.extractLsb' 0 2).toNat : Int) * 16).toNat = (imm.extractLsb' 0 2).toNat * 16 by
      omega]
    refine congrArg pure (BitVec.eq_of_getLsbD_eq fun k hk => ?_)
    rw [getLsbD_setSlice _ _ _ _ _ hk, pinsrwMmxSpec, getLsbD_ofLanes _ _ hk]
    rw [ite_eq_left (show k < 64 / 16 * 16 by omega)]
    generalize (imm.extractLsb' 0 2).toNat = j at *
    by_cases hin : j * 16 ≤ k ∧ k < j * 16 + 16
    · rw [ite_eq_left hin, ite_eq_left (show k / 16 = j by omega),
        show k - j * 16 = k % 16 by omega]
    · rw [ite_eq_right hin, ite_eq_right (show ¬ k / 16 = j by omega)]
      simp only [lane, BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 16),
        decide_true, Bool.true_and]
      rw [Nat.mul_comm, Nat.div_add_mod]

end X86Proofs
