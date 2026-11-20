import X86Proofs.Core.Runtime

/-!
# MOVD, MOVQ (between XMM and general-purpose registers) specification

`MOVD xmm, r32` / `MOVQ xmm, r64` (`66 0F 6E /r`, REX.W for MOVQ): the XMM register becomes the
general-purpose register zero-extended, `DEST[31:0] ← SRC[31:0]; DEST[127:32] ← 0` (`[63:0]` for
MOVQ). `MOVD r32, xmm` / `MOVQ r64, xmm` (`66 0F 7E /r`): the general-purpose register becomes
the low doubleword (quadword) of the XMM register. `movdSpec e n src` is the low `e` bits of
`src` zero-extended to `n` bits; lean-x86 computes it with `Operations.MOV_WDQ e m n`. No flags.
-/

namespace X86Proofs

/-- The low `e` bits of `src`, zero-extended to `n` bits. -/
def movdSpec (e n : Nat) {m : Nat} (src : BitVec m) : BitVec n :=
  (src.extractLsb' 0 e).setWidth n

open X86

theorem mov_wdq_operation (e m n : Nat) (hm : e ≤ m) (hn : e ≤ n) (he : 0 < e)
    (src : BitVec m) :
    X86.Instructions.Operations.MOV_WDQ e m n src = .ok (movdSpec e n src) := by
  unfold X86.Instructions.Operations.MOV_WDQ
  simp (disch := omega) [x86_runtime, movdSpec]
  rfl

end X86Proofs
