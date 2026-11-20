import X86Proofs.Core.Lanes

/-!
# MOVMSKPS, MOVMSKPD, PMOVMSKB specification

`MOVMSKPS`/`MOVMSKPD`/`PMOVMSKB r32, xmm` (`0F 50`, `66 0F 50`, `66 0F D7 /r`): gather the sign
bit of each doubleword, quadword or byte of the source into the low bits of the destination,
`DEST[0] ← SRC[31]; DEST[1] ← SRC[63]; …; DEST[31:4] ← 0` (MOVMSKPS; MOVMSKPD and PMOVMSKB
likewise for 2 and 16 lanes). `movmskSpec w` is the result for lanes of `w` bits; lean-x86
computes it with `Operations.MOVMSK w 128 32`. No flags.

The MMX form (`NP 0F D7`, `PMOVMSKB r32, mm`) takes the 8 byte sign bits of a 64-bit value:
`movmskMmxSpec`.
-/

namespace X86Proofs

/-- Bit `i` of the result is the sign bit of lane `i` of `a` (`SRC[i * w + w - 1]`), for each of
the `128 / w` lanes; the bits above are zero. -/
def movmskSpec (w : Nat) (a : BitVec 128) : BitVec 32 :=
  (ofLanes (128 / w) 1 fun i => a.extractLsb' (i * w + (w - 1)) 1).setWidth 32

/-- The MMX form (`PMOVMSKB r32, mm`, `NP 0F D7`): bit `i` of the result is the sign bit of byte `i`
of `a`, for each of the 8 bytes; the bits above are zero. -/
def movmskMmxSpec (a : BitVec 64) : BitVec 32 :=
  (ofLanes 8 1 fun i => a.extractLsb' (i * 8 + 7) 1).setWidth 32

open X86 X86.Runtime

theorem movmsk_operation (w : Nat) (hw : w = 8 ∨ w = 32 ∨ w = 64) (a : BitVec 128) :
    X86.Instructions.Operations.MOVMSK w 128 32 a = .ok (movmskSpec w a) := by
  generalize hv : (fun i => a.extractLsb' (i * w + (w - 1)) 1) = v
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.MOVMSK
    simp only [x86_runtime, pure_bind, Int.reduceDiv]
    rw [forIn_writeSlice _ ?hk v _ ?h]
    case hk => rfl
    case h =>
      intro i hi p u
      simp (disch := lanes_disch) only [x86_runtime, pure_bind, writeSlice_mk,
        Int.toNat_natCast, Int.toNat_add, Int.toNat_mul, Int.reduceToNat, Nat.mul_one,
        Nat.reduceSub, ← hv]
      rfl
    simp only [Except.bind, bind, pure, Except.pure]
    rw [read_mk _ _ (by decide) rfl, movmskSpec, hv]
    rfl

theorem movmsk_mmx_operation (a : BitVec 64) :
    X86.Instructions.Operations.MOVMSK 8 64 32 a = .ok (movmskMmxSpec a) := by
  generalize hv : (fun i => a.extractLsb' (i * 8 + 7) 1) = v
  unfold X86.Instructions.Operations.MOVMSK
  simp only [x86_runtime, pure_bind, Int.reduceDiv]
  rw [forIn_writeSlice _ ?hk v _ ?h]
  case hk => rfl
  case h =>
    intro i hi p u
    simp (disch := lanes_disch) only [x86_runtime, pure_bind, writeSlice_mk,
      Int.toNat_natCast, Int.toNat_add, Int.toNat_mul, Int.reduceToNat, Nat.mul_one, ← hv]
    rfl
  simp only [Except.bind, bind, pure, Except.pure]
  rw [read_mk _ _ (by decide) rfl, movmskMmxSpec, hv]
  rfl

end X86Proofs
