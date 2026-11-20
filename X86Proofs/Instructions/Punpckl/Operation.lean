import X86Proofs.Core.Lanes

/-!
# PUNPCKLBW, PUNPCKLWD, PUNPCKLDQ, PUNPCKLQDQ specification

`PUNPCKLBW`/`PUNPCKLWD`/`PUNPCKLDQ`/`PUNPCKLQDQ xmm1, xmm2/m128` (`66 0F 60`/`61`/`62`/`6C /r`):
interleave the low halves of the destination and the source, lane by lane: `DEST[7:0] ←
DEST[7:0]; DEST[15:8] ← SRC[7:0]; DEST[23:16] ← DEST[15:8]; DEST[31:24] ← SRC[15:8]; …` (for
bytes; words, doublewords and the quadword likewise). `punpcklSpec w` is the result for lanes of
`w` bits (`Operations.UNPCKL_lanes w 128`). No flags.

The MMX forms (`NP 0F 60`/`61`/`62`) interleave the low halves of an MMX register and an MMX
register or 32 bits of memory, lean-x86's `Operations.PUNPCKL_reg` and `PUNPCKL_mem`:
`punpcklMmxSpec`.
-/

namespace X86Proofs

/-- Lane `i` of the result is lane `i / 2` of `a` for even `i`, of `b` for odd `i`. -/
def punpcklSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i =>
    if i % 2 = 0 then lane w a (i / 2) else lane w b (i / 2)

/-- The MMX forms (`PUNPCKLBW`/`WD`/`DQ mm, mm/m32`): lane `i` of the result is lane `i / 2` of
the destination `a` for even `i`, of the source `b` (an MMX register, or 32 bits of memory) for
odd `i`. -/
def punpcklMmxSpec (w : Nat) {n : Nat} (a : BitVec 64) (b : BitVec n) : BitVec 64 :=
  ofLanes 64 w fun i => if i % 2 = 0 then lane w a (i / 2) else lane w b (i / 2)

open X86

theorem punpckl_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.UNPCKL_lanes w 128 a b = .ok (punpcklSpec w a b) := by
  rw [← ofLanes_full (by decide) (punpcklSpec w a b)]
  rcases hw with rfl | rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.UNPCKL_lanes
    simp only [x86_runtime, pure_bind, bind_pure, Int.reduceDiv]
    refine forIn_ofLanes _ _ _ (by rfl) _ _ (fun l hl r => ?_)
    obtain rfl : l = 0 := by omega
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, Nat.zero_mul, Int.zero_mul,
      Int.cast_ofNat_Int, BitVec.extractLsb'_eq_self, setSlice_full]
    refine forIn_ofLanes_yield _ _ _ (by rfl) _ _ (fun i hi r => ?_)
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul,
      Int.toNat_natCast, toNat_natCast_ediv, Int.reduceToNat]
    simp only [bind, Except.bind, lane]
    by_cases h : i % 2 = 0
    · rw [ite_eq_left (by simp; omega), ite_eq_left h]; rfl
    · rw [ite_eq_right (by simp; omega), ite_eq_right h]; rfl

theorem punpckl_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 64) :
    X86.Instructions.Operations.PUNPCKL_reg w a b = .ok (punpcklMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PUNPCKL_reg
    lanes_loop
    rename_i i hi r
    simp only [bind, Except.bind]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega

theorem punpckl_mmx_mem_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a : BitVec 64)
    (b : BitVec 32) :
    X86.Instructions.Operations.PUNPCKL_mem w a b = .ok (punpcklMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PUNPCKL_mem
    lanes_loop
    rename_i i hi r
    simp only [bind, Except.bind]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega

end X86Proofs
