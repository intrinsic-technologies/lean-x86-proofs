import X86Proofs.Step.FetchImm

namespace X86Proofs

def encodeMovMoffs64Rax (moffs : BitVec 64) : List UInt8 :=
  0x48 :: 0xA3 :: immBytes 64 moffs

def encodeMovMoffs32Eax (moffs : BitVec 64) : List UInt8 :=
  0xA3 :: immBytes 64 moffs

def encodeMovMoffs16Ax (moffs : BitVec 64) : List UInt8 :=
  0x66 :: 0xA3 :: immBytes 64 moffs

def encodeMovMoffs8Al (moffs : BitVec 64) : List UInt8 :=
  0xA2 :: immBytes 64 moffs

def encodeMovMoffs64RaxA32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0x48 :: 0xA3 :: immBytes 32 moffs

def encodeMovMoffs32EaxA32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0xA3 :: immBytes 32 moffs

def encodeMovMoffs16AxA32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0x66 :: 0xA3 :: immBytes 32 moffs

def encodeMovMoffs8AlA32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0xA2 :: immBytes 32 moffs

end X86Proofs
