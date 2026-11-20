import X86Proofs.Core.Lanes

/-!
# PCMPEQB, PCMPEQW, PCMPEQD specification

`PCMPEQB`/`PCMPEQW`/`PCMPEQD xmm1, xmm2/m128` (`66 0F 74`/`75`/`76 /r`): compare the packed
lanes for equality, `IF DEST[7:0] = SRC[7:0] THEN DEST[7:0] ← FFH ELSE DEST[7:0] ← 0` and so on.
`pcmpeqSpec w` is the result for lanes of `w` bits (`Operations.PCMPEQ w 128`). No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `pcmpeqMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is all ones if the lanes of `a` and `b` are equal, else zero. -/
def pcmpeqSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => if lane w a i = lane w b i then BitVec.allOnes w else 0

/-- `pcmpeqSpec` at 64 bits, for the MMX forms. -/
def pcmpeqMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => if lane w a i = lane w b i then BitVec.allOnes w else 0

open X86

theorem pcmpeq_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 128) :
    X86.Instructions.Operations.PCMPEQ w 128 a b = .ok (pcmpeqSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PCMPEQ
    lanes_loop
    simp only [beq_iff_eq]
    split <;> simp only [*, ↓reduceIte] <;> rfl

theorem pcmpeq_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32) (a b : BitVec 64) :
    X86.Instructions.Operations.PCMPEQ w 64 a b = .ok (pcmpeqMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PCMPEQ
    lanes_loop
    simp only [beq_iff_eq]
    split <;> simp only [*, ↓reduceIte] <;> rfl

end X86Proofs
