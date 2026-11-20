import X86Proofs.Core.Gpr
import X86Proofs.Core.Shift
import X86Proofs.Program.ComposeAttr

/-!
# CMPXCHG8B specification

`CMPXCHG8B m64` (Intel SDM): compare EDX:EAX with the 64-bit destination; if they are equal,
`ZF ← 1; DEST ← ECX:EBX`; else `ZF ← 0; EDX:EAX ← DEST`. CF, PF, AF, SF and OF are unaffected.
The destination is written either way (with its own value when the comparison fails). In 64-bit
mode the writes of EDX and EAX zero-extend into RDX and RAX; when the comparison succeeds RDX and
RAX are not written.
-/

namespace X86Proofs

/-- `hi:lo`: the 64-bit value whose upper half is the low 32 bits of `hi` and whose lower half is
the low 32 bits of `lo` (EDX:EAX from RDX and RAX, ECX:EBX from RCX and RBX). -/
def concat32 (hi lo : BitVec 64) : BitVec 64 := hi.setWidth 32 ++ lo.setWidth 32

/-- The new destination and the flags of `cmpxchg8b m` with `acc` = EDX:EAX and `rep` = ECX:EBX,
from the flags `f` before it: ECX:EBX if `acc = m`, else `m`'s own value; ZF set to whether they
are equal, the other flags kept. -/
def cmpxchg8bSpec (f : StatusFlags) (acc rep m : BitVec 64) : BitVec 64 × StatusFlags :=
  (if acc = m then rep else m, { f with ZF := decide (acc = m) })

open X86 X86.Helpers

theorem ofNat_concat32 (a b : BitVec 32) :
    BitVec.ofNat 64 ((a.toNat <<< 32) + b.toNat) = a ++ b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, BitVec.toNat_ofNat]
  have ha := a.isLt
  have hb := b.isLt
  rw [Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  simp only [Nat.reducePow] at ha hb ⊢
  omega

theorem cmpxchg8b_operation {σ : Type} (s : X86.State σ) (m : BitVec 64) :
    (X86.Instructions.Operations.CMPXCHG8B m).run s =
      let acc := concat32 s.GPR[gprIndex 2] s.GPR[gprIndex 0]
      let rep := concat32 s.GPR[gprIndex 1] s.GPR[gprIndex 3]
      let out := cmpxchg8bSpec (StatusFlags.ofRFLAGS s.RFLAGS) acc rep m
      if acc = m then (.ok out.1, setFlags s out.2)
      else (.ok out.1, setFlags { s with
        GPR := Vector.set (Vector.set s.GPR (gprIndex 2) ((m.extractLsb' 32 32).setWidth 64))
          (gprIndex 0) ((m.setWidth 32).setWidth 64) } out.2) := by
  unfold X86.Instructions.Operations.CMPXCHG8B
  spec_run [EDX => edx_run _, EAX => eax_run _]
  simp only [Int.reduceAdd, Int.reduceToNat, ofNat_concat32, beq_iff_eq]
  rw [show ∀ a b : BitVec 64, a.setWidth 32 ++ b.setWidth 32 = concat32 a b from fun _ _ => rfl]
  generalize concat32 s.GPR[gprIndex 2] s.GPR[gprIndex 0] = acc
  by_cases h : acc = m
  · simp only [h, ↓reduceIte, cmpxchg8bSpec, decide_true]
    spec_run [ECX => ecx_run _, EBX => ebx_run _]
    simp only [Int.reduceAdd, Int.reduceToNat, ofNat_concat32]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext
  · simp only [h, ↓reduceIte, cmpxchg8bSpec, decide_false]
    spec_run [EDX_write => edxWrite_run _ _, EAX_write => eaxWrite_run _ _]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem cmpxchg8b_operation_eq {σ : Type} (s : X86.State σ) (m : BitVec 64)
    (h : concat32 s.GPR[gprIndex 2] s.GPR[gprIndex 0] = m) :
    (X86.Instructions.Operations.CMPXCHG8B m).run s =
      (.ok (concat32 s.GPR[gprIndex 1] s.GPR[gprIndex 3]),
        setFlags s { StatusFlags.ofRFLAGS s.RFLAGS with ZF := true }) := by
  rw [cmpxchg8b_operation]
  simp only [cmpxchg8bSpec, h, ↓reduceIte, decide_true]

theorem cmpxchg8b_operation_ne {σ : Type} (s : X86.State σ) (m : BitVec 64)
    (h : ¬ concat32 s.GPR[gprIndex 2] s.GPR[gprIndex 0] = m) :
    (X86.Instructions.Operations.CMPXCHG8B m).run s =
      (.ok m, setFlags { s with
        GPR := Vector.set (Vector.set s.GPR (gprIndex 2) ((m.extractLsb' 32 32).setWidth 64))
          (gprIndex 0) ((m.setWidth 32).setWidth 64) }
        { StatusFlags.ofRFLAGS s.RFLAGS with ZF := false }) := by
  rw [cmpxchg8b_operation]
  simp only [cmpxchg8bSpec, h, ↓reduceIte, decide_false]

attribute [x86_compose] concat32

end X86Proofs
