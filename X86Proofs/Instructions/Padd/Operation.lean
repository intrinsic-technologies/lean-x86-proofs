import X86Proofs.Core.Lanes

/-!
# PADDB, PADDW, PADDD, PADDQ specification

`PADDB`/`PADDW`/`PADDD`/`PADDQ xmm1, xmm2/m128` (`66 0F FC`/`FD`/`FE`/`D4 /r`): add the packed
bytes, words, doublewords or quadwords lane by lane, `DEST[7:0] ← DEST[7:0] + SRC[7:0]` and so on
for every lane, wrapping (the carry out of a lane is lost). `paddSpec w` is the result for lanes
of `w` bits; lean-x86 computes it with `Operations.PADD w 128`. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `paddMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the sum of the lanes of `a` and `b`, wrapping. -/
def paddSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => lane w a i + lane w b i

/-- `paddSpec` at 64 bits, for the MMX forms. -/
def paddMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => lane w a i + lane w b i

open X86

theorem padd_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.PADD w 128 a b = .ok (paddSpec w a b) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PADD
    lanes_loop

theorem padd_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 64) :
    X86.Instructions.Operations.PADD w 64 a b = .ok (paddMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PADD
    lanes_loop

end X86Proofs
