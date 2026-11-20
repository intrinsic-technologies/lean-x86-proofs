import X86Proofs.Core.Gpr
import X86Proofs.Core.Shift
import X86Proofs.Program.ComposeAttr

/-!
# CMPXCHG16B specification

`CMPXCHG16B m128` (Intel SDM): compare RDX:RAX with the 128-bit destination; if they are equal,
`ZF ← 1; DEST ← RCX:RBX`; else `ZF ← 0; RDX:RAX ← DEST`. CF, PF, AF, SF and OF are unaffected. The
destination is written either way (with its own value when the comparison fails); when the
comparison succeeds RDX and RAX are not written.
-/

namespace X86Proofs

/-- The new destination and the flags of `cmpxchg16b m` with `acc` = RDX:RAX and `rep` = RCX:RBX,
from the flags `f` before it: RCX:RBX if `acc = m`, else `m`'s own value; ZF set to whether they are
equal, the other flags kept. -/
def cmpxchg16bSpec (f : StatusFlags) (acc rep m : BitVec 128) : BitVec 128 × StatusFlags :=
  (if acc = m then rep else m, { f with ZF := decide (acc = m) })

open X86 X86.Helpers

theorem ofNat_concat64 (a b : BitVec 64) :
    BitVec.ofNat 128 ((a.toNat <<< 64) + b.toNat) = a ++ b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, BitVec.toNat_ofNat]
  have ha := a.isLt
  have hb := b.isLt
  rw [Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  simp only [Nat.reducePow] at ha hb ⊢
  omega

theorem cmpxchg16b_operation_eq {σ : Type} (s : X86.State σ) (m : BitVec 128)
    (h : s.GPR[gprIndex 2] ++ s.GPR[gprIndex 0] = m) :
    (X86.Instructions.Operations.CMPXCHG16B m).run s =
      (.ok (s.GPR[gprIndex 1] ++ s.GPR[gprIndex 3]),
        setFlags s { StatusFlags.ofRFLAGS s.RFLAGS with ZF := true }) := by
  unfold X86.Instructions.Operations.CMPXCHG16B
  spec_run [RDX => rdx_run _, RAX => rax_run _]
  simp only [Int.reduceAdd, Int.reduceToNat, ofNat_concat64, h, beq_self_eq_true, ↓reduceIte]
  spec_run [RCX => rcx_gpr_run _, RBX => rbx_run _]
  simp only [Int.reduceAdd, Int.reduceToNat, ofNat_concat64]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

theorem cmpxchg16b_operation_ne {σ : Type} (s : X86.State σ) (m : BitVec 128)
    (h : ¬ s.GPR[gprIndex 2] ++ s.GPR[gprIndex 0] = m) :
    (X86.Instructions.Operations.CMPXCHG16B m).run s =
      (.ok m, setFlags { s with
        GPR := Vector.set (Vector.set s.GPR (gprIndex 2) (m.extractLsb' 64 64))
          (gprIndex 0) (m.setWidth 64) }
        { StatusFlags.ofRFLAGS s.RFLAGS with ZF := false }) := by
  unfold X86.Instructions.Operations.CMPXCHG16B
  spec_run [RDX => rdx_run _, RAX => rax_run _]
  simp only [Int.reduceAdd, Int.reduceToNat, ofNat_concat64, beq_iff_eq, h, ↓reduceIte]
  spec_run [RDX_write => rdxWrite_run _ _, RAX_write => raxWrite_run _ _]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

end X86Proofs
