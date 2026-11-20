import X86Proofs.Step.Address

/-!
# Encoding the multi-byte NOP

The bytes of `nop [mem]` (`0F 1F /0`) after any prefix bytes, for any `AddrMode`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `nop [am]` with prefixes `pre`: `pre, 0F, 1F, ModRM (reg = 0), am.tail`. -/
def encodeNopM (pre : List UInt8) (am : AddrMode) : List UInt8 :=
  pre ++ 0x0F :: 0x1F :: am.modrm 0 :: am.tail

end X86Proofs
