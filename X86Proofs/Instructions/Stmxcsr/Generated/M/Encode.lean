import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeStmxcsrM32 (am : AddrMode) : List UInt8 :=
  encodeSseMem 0xAE 3 am

end X86Proofs
