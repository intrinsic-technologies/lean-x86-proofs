import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.Escape
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSetccM8 (cc : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x0F :: setccOpcode cc :: am.modrm 0 :: am.tail
  else am.rexByte false 0 :: 0x0F :: setccOpcode cc :: am.modrm 0 :: am.tail

end X86Proofs
