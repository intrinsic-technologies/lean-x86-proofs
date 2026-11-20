import X86Proofs.Core.Lanes

/-!
# PSUBB, PSUBW, PSUBD, PSUBQ specification

`PSUBB`/`PSUBW`/`PSUBD`/`PSUBQ xmm1, xmm2/m128` (`66 0F F8`/`F9`/`FA`/`FB /r`): subtract the
packed lanes of the source from those of the destination, `DEST[7:0] ← DEST[7:0] − SRC[7:0]` and
so on, wrapping. `psubSpec w` is the result for lanes of `w` bits (`Operations.PSUB w 128`). No
flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits: `psubMmxSpec`.
-/

namespace X86Proofs

/-- Each `w`-bit lane of the result is the lane of `a` minus the lane of `b`, wrapping. -/
def psubSpec (w : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 w fun i => lane w a i - lane w b i

/-- `psubSpec` at 64 bits, for the MMX forms. -/
def psubMmxSpec (w : Nat) (a b : BitVec 64) : BitVec 64 :=
  ofLanes 64 w fun i => lane w a i - lane w b i

open X86

theorem psub_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 128) :
    X86.Instructions.Operations.PSUB w 128 a b = .ok (psubSpec w a b) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSUB
    lanes_loop

theorem psub_mmx_operation (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a b : BitVec 64) :
    X86.Instructions.Operations.PSUB w 64 a b = .ok (psubMmxSpec w a b) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  · unfold X86.Instructions.Operations.PSUB
    lanes_loop

end X86Proofs
