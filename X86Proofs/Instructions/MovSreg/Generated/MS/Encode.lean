import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeMovM16Sreg (sreg : BitVec 3) (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x8C :: am.modrm sreg :: am.tail
  else am.rexByte false 0 :: 0x8C :: am.modrm sreg :: am.tail

end X86Proofs
