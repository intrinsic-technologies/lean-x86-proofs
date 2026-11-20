import X86Proofs.Instructions.Xor.Generated.AccImm8.Step
import X86Proofs.Instructions.Xor.Generated.AccImm8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Xor.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xorAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (a ^^^ b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (xorFlags (a ^^^ b)) }

@[simp] theorem xorAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (s : RamState) :
    (xorAlImm8Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem xorAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (xorAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem xor_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x34 :: immBytes 8 imm))
      (xorAlImm8Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, xor_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), xor_al_imm8_ready h imm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0x34 :: immBytes 8 imm))
      (Effect.post (xorAlImm8Effect p imm)) :=
  Triple.of_effect (fun s _ => xorAlImm8Effect_avoids p _ s _)
    (xor_al_imm8_effect_step p imm)

theorem xor_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXorAlImm8 imm)) (Effect.post (xorAlImm8Effect p imm)) :=
  xor_al_imm8_triple_of_bytes p imm

attribute [x86_compose] xorAlImm8Effect

@[x86_local] theorem xorAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} :
    Effect.Local (xorAlImm8Effect p imm8) := by
  effect_local [xorAlImm8Effect]

end X86Proofs
