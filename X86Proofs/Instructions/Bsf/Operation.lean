import X86Proofs.Core.Bits
import X86Proofs.Core.Gpr

/-!
# BSF specification

`BSF DEST, SRC` (bit scan forward): for a non-zero source, `ZF ← 0` and `DEST` is the index of
the lowest set bit (`temp ← 0; WHILE Bit(SRC, temp) = 0 DO temp ← temp + 1; DEST ← temp`,
`lowestSetBit`). For a zero source, `ZF ← 1` and `DEST` is undefined; lean-x86 follows the
SDM's 092 note that the destination is then left unchanged (`Operations.BSF` returns, with the
result, whether to write it: `x != 0`; the form skips the write otherwise), and draws
the discarded result from its oracle (`n` bits). The SDM leaves CF, OF, SF, AF and PF undefined;
lean-x86 clears CF, OF, SF and AF and sets PF to the even parity of the whole source
(`bitScanFlags`, shared with BSR), so every flag is defined.
-/

namespace X86Proofs

/-- Flags of a bit scan of `x` (BSF, BSR): ZF says `x` is zero, PF is the even parity of `x`,
CF, OF, SF and AF are clear. -/
def bitScanFlags {n : Nat} (x : BitVec n) : StatusFlags :=
  { CF := false, OF := false, SF := false, AF := false, ZF := x == 0, PF := !oddBits x }

/-- Result and flags of `bsf x`: the index of the lowest set bit of `x` (written only for a
non-zero `x`). -/
def bsfSpec {n : Nat} (x : BitVec n) : BitVec n × StatusFlags :=
  (BitVec.ofNat n (lowestSetBit x), bitScanFlags x)

/-- The destination register after a bit scan of `x` at `n` bits with result `r`: unchanged for a
zero `x`, else `r` written at `n` bits (`mergeGPR`: zero-extended at 32 bits, merged into `old` at
16). -/
def bitScanDest (n : Nat) (x r : BitVec n) (old : BitVec 64) : BitVec 64 :=
  if x = 0 then old else mergeGPR n r old

open X86 X86.Helpers

theorem bsf_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x : BitVec n) :
    (X86.Instructions.Operations.BSF n x).run s =
      (.ok ((if x = 0 then (s.oracle.take n).1 else (bsfSpec x).1), x != 0),
        setFlags { s with oracle := oracleSkip s.oracle (if x = 0 then n else 0) }
          (bsfSpec x).2) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.BSF
    simp only [x86_runtime, pure_bind, countTrailingZeroBits_run, isParityOdd_run]
    by_cases hx : x = 0
    · subst hx
      simp only [beq_self_eq_true, ↓reduceIte]
      repeat spec_bind_rfl
      simp only [bsfSpec, bitScanFlags]
      generalize oddBits _ = p
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext
    · simp only [beq_eq_false_iff_ne.mpr hx, hx, ↓reduceIte, bne_iff_ne.mpr hx]
      repeat spec_bind_rfl
      simp only [bsfSpec, bitScanFlags, Int.pow_zero, Int.ediv_one, BitVec.ofInt_natCast]
      generalize oddBits _ = p
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

end X86Proofs
