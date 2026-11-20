import X86Proofs.Core.Lanes

/-!
# PSADBW specification

`PSADBW xmm1, xmm2/m128` (`66 0F F6 /r`): the sum of absolute differences of the unsigned bytes,
per quadword: `TEMP0 ← ABS(DEST[7:0] − SRC[7:0]); …; TEMP7 ← ABS(DEST[63:56] − SRC[63:56]);
DEST[15:0] ← SUM(TEMP0:TEMP7); DEST[63:16] ← 000000000000H`, and the same for bytes 8–15 into
bits 64–79. Each sum is at most `8 * 255`, so the quadword is the sum. `psadbwSpec` is lean-x86's
`Operations.PSADBW 128` (a loop over the two quadwords, summing in an integer). No flags.

The MMX form (`NP 0F F6 mm, mm/m64`) computes the same at 64 bits, one quadword: `psadbwMmxSpec`.
-/

namespace X86Proofs

/-- Quadword `i` of the result is the sum, over the bytes `8 i` to `8 i + 7`, of the absolute
differences of the bytes of `a` and `b` as unsigned numbers. -/
def psadbwSpec (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 64 fun i => BitVec.ofNat 64 ((List.range 8).map fun j =>
    ((lane 8 a (i * 8 + j)).toNat - (lane 8 b (i * 8 + j)).toNat : Int).natAbs).sum

/-- `psadbwSpec` at 64 bits, for the MMX form (`PSADBW mm, mm/m64`): one quadword, the sum of the
eight absolute byte differences. -/
def psadbwMmxSpec (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).map fun j =>
    ((lane 8 a j).toNat - (lane 8 b j).toNat : Int).natAbs).sum

open X86 X86.Runtime

theorem psadbw_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PSADBW 128 a b = .ok (psadbwSpec a b) := by
  unfold X86.Instructions.Operations.PSADBW
  simp only [x86_runtime, pure_bind, Int.reduceDiv]
  let d (i j : Nat) : Nat :=
    ((lane 8 a (i * 8 + j)).toNat - (lane 8 b (i * 8 + j)).toNat : Int).natAbs
  let v (i : Nat) : BitVec 64 := BitVec.ofNat 64 ((List.range 8).map (d i)).sum
  rw [forIn_lanes 2 _ _ (fun i r => match r with
      | .mk p u => .mk (setSlice p (i * 64) 64 (v i)) (setSlice u (i * 64) 64 0)) ?h]
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, empty_eq_mk]
    simp only [bind, Except.bind]
    rw [read_mk _ _ (by decide) (by decide)]
    rfl
  · intro i hi r
    rw [forIn_lanes 8 _ _ (fun j s => s + (d i j : Int)) ?h2]
    · cases r with
      | mk p u =>
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul, Int.toNat_natCast,
        Int.reduceToNat, writeSlice_mk, foldl_add_natAbs, Int.pow_zero, Int.ediv_one,
        Int.zero_add]
      rfl
    · intro j hj s
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul, Int.toNat_add,
        Int.toNat_natCast, Int.reduceToNat]
      rfl

theorem psadbw_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PSADBW 64 a b = .ok (psadbwMmxSpec a b) := by
  unfold X86.Instructions.Operations.PSADBW
  simp only [x86_runtime, pure_bind, Int.reduceDiv]
  let d (j : Nat) : Nat := ((lane 8 a j).toNat - (lane 8 b j).toNat : Int).natAbs
  let v : BitVec 64 := BitVec.ofNat 64 ((List.range 8).map d).sum
  rw [forIn_lanes 1 _ _ (fun i r => match r with
      | .mk p u => .mk (setSlice p (i * 64) 64 v) (setSlice u (i * 64) 64 0)) ?h]
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil,
      empty_eq_mk]
    simp only [bind, Except.bind]
    rw [read_mk _ _ (by decide) (by decide)]
    simp only [Nat.zero_mul]
    exact congrArg Except.ok (setSlice_full (0 : BitVec 64) v)
  · intro i hi r
    obtain rfl : i = 0 := by omega
    rw [forIn_lanes 8 _ _ (fun j s => s + (d j : Int)) ?h2]
    · cases r with
      | mk p u =>
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.reduceToNat, writeSlice_mk,
        foldl_add_natAbs, Int.pow_zero, Int.ediv_one, Int.zero_add, Nat.zero_mul, setSlice_full]
      rfl
    · intro j hj s
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, Int.toNat_mul, Int.toNat_add,
        Int.toNat_natCast, Int.reduceToNat, Nat.zero_add]
      rfl

end X86Proofs
