import X86Proofs.Core.Lanes

/-!
# PUNPCKHBW, PUNPCKHWD, PUNPCKHDQ, PUNPCKHQDQ specification

`PUNPCKHBW`/`PUNPCKHWD`/`PUNPCKHDQ`/`PUNPCKHQDQ xmm1, xmm2/m128` (`66 0F 68`/`69`/`6A`/`6D /r`):
interleave the high halves of the destination and the source, lane by lane: `DEST[7:0] ←
DEST[71:64]; DEST[15:8] ← SRC[71:64]; DEST[23:16] ← DEST[79:72]; …` (for bytes; words,
doublewords and the quadword likewise). `punpckhSpec w` is the result for lanes of `w` bits
(`Operations.UNPCKH_lanes w 128`): lane `i / 2` of the high half is lane `i / 2 + 64 / w`. No
flags.

The MMX forms (`NP 0F 68`/`69`/`6A`) interleave the high halves of two 64-bit operands, lean-x86's
`Operations.PUNPCKH_reg` and `PUNPCKH_mem`: `punpckhMmxSpec`.
-/

namespace X86Proofs

/-- Lane `i` of the result is lane `i / 2` of the high half of `a` for even `i`, of `b` for odd
`i`. -/
def punpckhSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i =>
    if i % 2 = 0 then lane w a (i / 2 + 64 / w) else lane w b (i / 2 + 64 / w)

/-- The MMX forms (`PUNPCKHBW`/`WD`/`DQ mm, mm/m64`): lane `i` of the result is lane
`i / 2 + 64 / w / 2` (the high half) of `a` for even `i`, of `b` for odd `i`. -/
def punpckhMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i =>
    if i % 2 = 0 then lane w a (i / 2 + 64 / w / 2) else lane w b (i / 2 + 64 / w / 2)

open X86

theorem punpckh_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.UNPCKH_lanes w 128 a b = .ok (punpckhSpec w a b) := by
  rw [← ofLanes_full (by decide) (punpckhSpec w a b)]
  rcases hw with rfl | rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.UNPCKH_lanes
    simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv]
    refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun l hl r => ?_)
    obtain rfl : l = 0 := by omega
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
      Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full]
    refine forIn_ofLanes_yield _ _ _ (by rfl) _ _ (fun i hi r => ?_)
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul, Int.toNat_add,
      Int.toNat_natCast, toNat_natCast_ediv, Int.reduceToNat]
    simp only [bind, Except.bind, lane, Nat.reduceDiv]
    by_cases h : i % 2 = 0
    · rw [ite_eq_left (by simp; omega), ite_eq_left h]; rfl
    · rw [ite_eq_right (by simp; omega), ite_eq_right h]; rfl

theorem punpckh_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 64) :
    X86.Instructions.Operations.PUNPCKH_reg w a b = .ok (punpckhMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PUNPCKH_reg
    lanes_loop
    rename_i i hi r
    simp only [bind, Except.bind]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega

theorem punpckh_mmx_mem_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 64) :
    X86.Instructions.Operations.PUNPCKH_mem w a b = .ok (punpckhMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PUNPCKH_mem
    lanes_loop
    rename_i i hi r
    simp only [bind, Except.bind]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega

end X86Proofs
