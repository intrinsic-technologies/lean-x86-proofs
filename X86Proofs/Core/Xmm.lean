import X86Proofs.Core.Mode

/-!
# XMM registers

lean-x86 keeps the vector registers as 32 ZMM registers of 512 bits (`State.ZMM`); XMM register
`r` is the low 128 bits of ZMM `r`. This file states what `Read_XMM` / `Write_XMM` do in 64-bit
mode at 128 bits, the size the legacy SSE forms use (`readXMM128_run`, `writeXMM128_run`), and
at other sizes: `readXMM_run` (a narrower read, the scalar forms), `writeXMM64_run` (a 64-bit
write zero-extended to 128 bits, MOVQ2DQ).

A legacy SSE write (no VEX or EVEX prefix, so `Write_XMM`'s `zero_upper` is `false`) replaces
the low 128 bits of the ZMM register and keeps bits 128–511 (`xmmMerge`). (A VEX/EVEX write would
also zero the upper bits; no such form is covered.) `xmmClear` is the part of a ZMM register that
an XMM write leaves alone: the register with its low 128 bits zeroed (`xmmClear_xmmMerge`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The slot of register number `r` in `State.ZMM`. -/
def xmmIndex (r : BitVec 5) : Fin 32 := ⟨r.toNat, r.isLt⟩

/-- How a legacy SSE write stores a 128-bit value `v` into a 512-bit ZMM register `old`, as
lean-x86's `XMM_write` does: the low 128 bits become `v`, bits 128–511 are kept. -/
def xmmMerge (v : BitVec 128) (old : BitVec 512) : BitVec 512 :=
  X86.Runtime.setSlice old 0 128 v

/-- A ZMM register with its XMM part (low 128 bits) zeroed: what an XMM write keeps. -/
def xmmClear (z : BitVec 512) : BitVec 512 := xmmMerge 0 z

theorem getLsbD_xmmMerge (v : BitVec 128) (z : BitVec 512) (i : Nat) :
    (xmmMerge v z).getLsbD i = if i < 128 then v.getLsbD i else z.getLsbD i := by
  unfold xmmMerge
  by_cases h5 : i < 512
  · rw [getLsbD_setSlice _ _ _ _ _ h5]
    by_cases h : i < 128 <;> simp [h]
  · have h : ¬ i < 128 := by omega
    simp [h, BitVec.getLsbD_of_ge z i (by omega),
      BitVec.getLsbD_of_ge (X86.Runtime.setSlice z 0 128 v) i (by omega)]

/-- The XMM part of a merged register is the value written. -/
@[simp] theorem xmmMerge_setWidth (v : BitVec 128) (z : BitVec 512) :
    (xmmMerge v z).setWidth 128 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [getLsbD_xmmMerge, hi]

/-- A second XMM write overrides the first. -/
@[simp] theorem xmmMerge_xmmMerge (v w : BitVec 128) (z : BitVec 512) :
    xmmMerge v (xmmMerge w z) = xmmMerge v z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [getLsbD_xmmMerge]
  split <;> rfl

/-- An XMM write keeps bits 128–511. -/
@[simp] theorem xmmClear_xmmMerge (v : BitVec 128) (z : BitVec 512) :
    xmmClear (xmmMerge v z) = xmmClear z :=
  xmmMerge_xmmMerge 0 v z

/-- In 64-bit mode, `Read_XMM r 128` returns the low 128 bits of ZMM register `r` and leaves the
state unchanged. -/
theorem readXMM128_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (mode : In64BitMode s) :
    (Read_XMM r 128).run s = (.ok (s.ZMM[xmmIndex r].setWidth 128), s) := by
  unfold Read_XMM
  simp only [x86_runtime, show (0 : Int) ≤ 128 from by decide,
    show (128 : Int) ≤ 128 from by decide, decide_true, pure_bind]
  rw [specM_bind_run _ _ mode]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp [XMM, X86.ZMM.get, x86_runtime, X86.Runtime.CheckedSlice.read, hindex, xmmIndex]
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  rfl

/-- In 64-bit mode, `Read_XMM r size` (`size ≤ 128`, e.g. 32 or 64 for a scalar floating-point
source, ADDSS `xmm, xmm`) returns the low `size` bits of ZMM register `r` and leaves the state
unchanged. -/
theorem readXMM_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (size : Int) (h0 : 0 ≤ size)
    (h1 : size ≤ 128) (mode : In64BitMode s) :
    (Read_XMM r size).run s = (.ok (s.ZMM[xmmIndex r].setWidth size.toNat), s) := by
  unfold Read_XMM
  simp only [x86_runtime, h0, h1, decide_true, pure_bind]
  rw [specM_bind_run _ _ mode]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  have hs : size.toNat ≤ 128 := by omega
  simp [XMM, X86.ZMM.get, x86_runtime, X86.Runtime.CheckedSlice.read, hindex, xmmIndex, h0, h1]
  rw [BitVec.setWidth_eq_extractLsb' (by omega)]
  rfl

/-- In 64-bit mode, a legacy SSE `Write_XMM r v false` (128-bit `v`, `zero_upper = false`) sets
the low 128 bits of ZMM register `r` to `v`, keeps its upper bits, and changes nothing else. -/
theorem writeXMM128_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (v : BitVec 128)
    (mode : In64BitMode s) :
    (Write_XMM (size := 128) r v false).run s =
      (.ok (), { s with ZMM := Vector.set s.ZMM (xmmIndex r) (xmmMerge v s.ZMM[xmmIndex r]) }) := by
  unfold Write_XMM
  simp only [x86_runtime, show (0 : Int) ≤ 128 from by decide,
    show (128 : Int) ≤ 128 from by decide, decide_true, pure_bind]
  rw [specM_bind_run _ _ mode]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp [XMM_write, X86.ZMM.get, X86.ZMM.set, x86_runtime, hindex, xmmIndex, xmmMerge]
  rfl

/-- `writeXMM128_run` for a 64-bit value (`Write_XMM (size := 64) r v false`, MOVQ2DQ): the value
zero-extended to 128 bits becomes the low 128 bits of ZMM register `r`. -/
theorem writeXMM64_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (v : BitVec 64)
    (mode : In64BitMode s) :
    (Write_XMM (size := 64) r v false).run s =
      (.ok (), { s with
        ZMM := Vector.set s.ZMM (xmmIndex r) (xmmMerge (v.setWidth 128) s.ZMM[xmmIndex r]) }) := by
  unfold Write_XMM
  simp only [x86_runtime, show (0 : Int) ≤ 64 from by decide,
    show (64 : Int) ≤ 128 from by decide, decide_true, pure_bind]
  rw [specM_bind_run _ _ mode]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp [XMM_write, X86.ZMM.get, X86.ZMM.set, x86_runtime, hindex, xmmIndex, xmmMerge]
  rfl

end X86Proofs
