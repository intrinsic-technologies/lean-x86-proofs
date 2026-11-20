import X86Proofs.Instructions.Movs.RepTriple
import X86Proofs.Program.Execution

/-!
# REP MOVSQ as runner execution

The REP MOVSQ triple (`RepTriple.lean`) counts its iterations as steps; here the same loop as a
runner execution (`Advances`, `Program/Execution.lean`): `rep_movsq_advances` takes `max count 1`
steps (a zero count still takes one step) without reaching the return boundary, and
`rep_movsq_copy` gives the copied bytes at the end, as `Option`s, so allocation is copied too.
-/

namespace X86Proofs
open X86 X86.Machine X86.UserProcess

/-- The checked REP loop consists of actual runner steps, including the final iteration. -/
theorem ReadyRepLoop.advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (boundary : ReturnBoundary)
    (count : Nat) (s : RamState) (h : ReadyRepLoop rex s (count + 1))
    (hstart : s.RIP ≠ boundary.rip) (hend : BitVec.add s.RIP 3#64 ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hs := h.step hstride hrex (by omega)
    have hi : (repMovsqAfter s).RIP ≠ boundary.rip := by
      rw [repMovsqAfter_rip s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inl hi)
  | succ k ih =>
    have hs := h.step hstride hrex (by omega)
    have hrip : (repMovsqAfter s).RIP = s.RIP := by
      rw [repMovsqAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega)
        (by have := h.srcLow; omega), ↓reduceIte]
    have ha : Advances boundary 1 s (repMovsqAfter s) :=
      Advances.of_step hs (.inl (by rw [hrip]; exact hstart))
    have hb := ih (repMovsqAfter s) h.next (by rw [hrip]; exact hstart)
      (by rw [hrip]; exact hend)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

/-- The zero-count case also consumes one real step and advances past REP. -/
theorem rep_movsq_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, rex, 0xa5]) s)
    (hpre : RepMovsqPre p s) (hstart : p ≠ boundary.rip) (hend : p + 3#64 ≠ boundary.rip) :
    Advances boundary (max (rcx.read s).toNat 1) s (nextStates (max (rcx.read s).toNat 1) s) := by
  have hcodeS : BytesAt s s.RIP [0xf3, rex, 0xa5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_movsq_step_zero s h.midRep rex hrex hcodeS hlow hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    apply Advances.of_step hs
    left
    rw [repMovsqZeroAfter_rip s h.ready.msr, hpre.rip]
    exact hend
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact hr.advances hstride hrex boundary k s (hpre.rip ▸ hstart) (hpre.rip ▸ hend)

/-- REP copies allocated bytes as `Option`s, retaining allocation as well as their values. -/
theorem rep_movsq_copy [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, rex, 0xa5]) s)
    (hpre : RepMovsqPre p s) :
    ∀ i < 8 * (rcx.read s).toNat,
      (nextStates (max (rcx.read s).toNat 1) s).external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rcases hn : (rcx.read s).toNat with _ | k
  · intro i hi; omega
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
        hpre.rip ▸ hcode.low (by simp) (by simp), hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact (rep_movsq_loop hstride hrex k s hr).copy

end X86Proofs
