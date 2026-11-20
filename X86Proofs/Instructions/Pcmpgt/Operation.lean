import X86Proofs.Core.Lanes

/-!
# PCMPGTB, PCMPGTW, PCMPGTD specification

`PCMPGTB`/`PCMPGTW`/`PCMPGTD xmm1, xmm2/m128` (`66 0F 64`/`65`/`66 /r`): compare the packed
signed lanes, `IF DEST[7:0] > SRC[7:0] THEN DEST[7:0] ← FFH ELSE DEST[7:0] ← 0` and so on, as
signed integers. `pcmpgtSpec w` is the result for lanes of `w` bits (`Operations.PCMPGT w 128`).
No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pcmpgtMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is all ones if the lane of `a` is greater than that of `b` as
a signed integer, else zero. -/
def pcmpgtSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => if (lane w a i).toInt > (lane w b i).toInt then BitVec.allOnes w else 0

/-- `pcmpgtSpec` at 64 bits, for the MMX forms. -/
def pcmpgtMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => if (lane w a i).toInt > (lane w b i).toInt then BitVec.allOnes w else 0

open X86

theorem pcmpgt_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 128) :
    X86.Instructions.Operations.PCMPGT w 128 a b = .ok (pcmpgtSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PCMPGT
    lanes_loop
    split <;> simp only [*, ↓reduceIte] <;> rfl

theorem pcmpgt_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 64) :
    X86.Instructions.Operations.PCMPGT w 64 a b = .ok (pcmpgtMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PCMPGT
    lanes_loop
    split <;> simp only [*, ↓reduceIte] <;> rfl

end X86Proofs
