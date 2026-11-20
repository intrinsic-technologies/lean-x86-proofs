import X86Proofs.Core.Lanes

/-!
# PAVGB, PAVGW specification

`PAVGB`/`PAVGW xmm1, xmm2/m128` (`66 0F E0`/`E3 /r`): average the packed unsigned bytes or words,
rounding up: `DEST[7:0] ← (SRC[7:0] + DEST[7:0] + 1) >> 1` with a 9-bit (17-bit) temporary, and
so on. `pavgSpec w` is the result for lanes of `w` bits (`Operations.PAVG w 128`). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pavgMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the rounded-up average of the lanes as unsigned numbers. -/
def pavgSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => BitVec.ofNat w (((lane w a i).toNat + (lane w b i).toNat + 1) / 2)

/-- `pavgSpec` at 64 bits, for the MMX forms. -/
def pavgMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => BitVec.ofNat w (((lane w a i).toNat + (lane w b i).toNat + 1) / 2)

open X86

theorem pavg_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 128) :
    X86.Instructions.Operations.PAVG w 128 a b = .ok (pavgSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PAVG
    lanes_loop
    lane_eq
    rw [← BitVec.ofInt_natCast]
    congr 1 <;> omega

theorem pavg_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16) (a b : BitVec 64) :
    X86.Instructions.Operations.PAVG w 64 a b = .ok (pavgMmxSpec w a b) := by
  rcases hw with rfl | rfl <;>
  · unfold X86.Instructions.Operations.PAVG
    lanes_loop
    lane_eq
    rw [← BitVec.ofInt_natCast]
    congr 1 <;> omega

end X86Proofs
