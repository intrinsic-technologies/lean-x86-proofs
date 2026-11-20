import X86

/-!
# PXOR, XORPS, XORPD specification

`PXOR xmm1, xmm2/m128` (`66 0F EF /r`), `XORPS` (`0F 57`) and `XORPD` (`66 0F 57`):
`DEST ← DEST XOR SRC`, all 128 bits; lean-x86 computes all three with `Operations.PXOR`. Bitwise:
no MXCSR access. No flags.

The MMX forms (`NP 0F … mm, mm/m64`) compute the same at 64 bits.
-/

namespace X86Proofs

theorem pxor_operation (a b : BitVec 128) :
    X86.Instructions.Operations.PXOR 128 a b = .ok (a ^^^ b) := rfl

theorem pxor_mmx_operation (a b : BitVec 64) :
    X86.Instructions.Operations.PXOR 64 a b = .ok (a ^^^ b) := rfl

end X86Proofs
