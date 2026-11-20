import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeSqrtssXmmM32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMem 0x51 dst am

end X86Proofs
