import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

def encodeMovM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)
  else am.rexByte false 0 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)

end X86Proofs
