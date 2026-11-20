import X86Proofs.Instructions.Cmp.Operation
import X86Proofs.Core.Gpr

/-!
# CMPXCHG specification

`CMPXCHG DEST, SRC` (Intel SDM): compare the accumulator (AL, AX, EAX or RAX) with DEST, setting
the flags as `CMP accumulator, DEST` does; if they are equal, `ZF ← 1; DEST ← SRC`; else
`ZF ← 0; accumulator ← DEST` (and a memory DEST is written back with its own value).
`cmpxchgSpec acc dst src` is the new DEST and the flags; when the comparison fails the accumulator
gets `dst`.

lean-x86 writes the accumulator only when the comparison fails (`Write_RAX`, which zero-extends
RAX at 32 bits) and a register DEST only when it succeeds, so at 32 bits the upper half of
whichever register is not written is kept.
-/

namespace X86Proofs

/-- The new DEST and the flags of `cmpxchg dst, src` with accumulator `acc`: SRC if `acc = dst`,
else DEST's own value; the flags of `cmp acc, dst`. -/
def cmpxchgSpec {n : Nat} (acc dst src : BitVec n) : BitVec n × StatusFlags :=
  (if acc = dst then src else dst, cmpSpec acc dst)

open X86 X86.Helpers

set_option maxHeartbeats 1000000 in
theorem cmpxchg_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (d src : BitVec n) (mem : Bool) :
    (X86.Instructions.Operations.CMPXCHG n d src mem).run s =
      let acc := s.GPR[gprIndex 0].setWidth n
      let gpr := Vector.set s.GPR (gprIndex 0) (mergeGPR n d s.GPR[gprIndex 0])
      if acc = d then (.ok ((cmpxchgSpec acc d src).1, true), setFlags s (cmpxchgSpec acc d src).2)
      else (.ok ((cmpxchgSpec acc d src).1, mem),
        setFlags { s with GPR := gpr } (cmpxchgSpec acc d src).2) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.CMPXCHG
    simp only [isParityEven8_run]
    spec_run [RAX => rax_run s]
    simp only [Int.reduceToNat, Int.toNat_natCast]
    simp (disch := decide) only [extractLsb'_zero_eq_setWidth]
    generalize s.GPR[gprIndex 0].setWidth _ = acc
    by_cases h : acc = d
    · subst h
      simp [x86_runtime, -BitVec.toInt_sub, -BitVec.toNat_sub, setFlags, StatusFlags.store,
        cmpxchgSpec, cmpSpec, subSpec]
      rfl
    · have hc : ¬ acc - d = BitVec.ofNat _ 0 :=
        fun h' => h (by simpa [BitVec.sub_eq_iff_eq_add] using h')
      simp only [h, cmpxchgSpec, ↓reduceIte]
      simp only [Int.cast_ofNat_Int, unsigned_eq, BitVec.ofNat_eq_ofNat, Int.toNat_one,
        BitVec.toNat_ofNat, Nat.pow_one, Nat.zero_mod, Int.add_zero, Int.pow_zero, Int.ediv_one,
        ofInt_sub_toNat, Int.reduceToNat, beq_iff_eq, hc, ↓reduceIte]
      spec_bind_rfl
      spec_bind_with (writeRAX_run_of_nat s _ (by decide) _)
      repeat spec_bind_rfl
      simp [x86_runtime, ofInt4_sub_toNat, toNat_sub_eq_iff, toNat_sub_mod16_eq_iff,
        -BitVec.toInt_sub, -BitVec.toNat_sub, extractLsb'_msb, beq_zero_eq_decide, setFlags,
        StatusFlags.store, cmpSpec, subSpec]
      congr 2
      rw [ite_zero_one, ite_zero_one, ite_zero_one, ite_one_zero, ite_one_zero]
      simp only [← Nat.not_le, decide_not, Bool.decide_eq_true]

theorem cmpxchg_operation_eq {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (acc d src : BitVec n) (mem : Bool)
    (hacc : s.GPR[gprIndex 0].setWidth n = acc) (h : acc = d) :
    (X86.Instructions.Operations.CMPXCHG n d src mem).run s =
      (.ok (src, true), setFlags s (cmpSpec acc d)) := by
  subst hacc
  rw [cmpxchg_operation s n hn d src mem, ite_eq_left_of_eq_true _ _ (eq_true h)]
  simp only [cmpxchgSpec, h, ↓reduceIte]

theorem cmpxchg_operation_ne {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (acc d src : BitVec n) (mem : Bool)
    (hacc : s.GPR[gprIndex 0].setWidth n = acc) (h : ¬ acc = d) :
    (X86.Instructions.Operations.CMPXCHG n d src mem).run s =
      let gpr := Vector.set s.GPR (gprIndex 0) (mergeGPR n d s.GPR[gprIndex 0])
      (.ok (d, mem), setFlags { s with GPR := gpr } (cmpSpec acc d)) := by
  subst hacc
  rw [cmpxchg_operation s n hn d src mem, ite_eq_right_of_eq_false _ _ (eq_false h)]
  simp only [cmpxchgSpec, h, ↓reduceIte]

end X86Proofs
