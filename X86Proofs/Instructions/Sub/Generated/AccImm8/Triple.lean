import X86Proofs.Instructions.Sub.Generated.AccImm8.Step
import X86Proofs.Instructions.Sub.Generated.AccImm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def subAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (a - b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (s : RamState) :
    (subAlImm8Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem subAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (subAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x2C :: immBytes 8 imm))
      (subAlImm8Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_al_imm8_ready h imm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0x2C :: immBytes 8 imm))
      (Effect.post (subAlImm8Effect p imm)) :=
  Triple.of_effect (fun s _ => subAlImm8Effect_avoids p _ s _)
    (sub_al_imm8_effect_step p imm)

theorem sub_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubAlImm8 imm)) (Effect.post (subAlImm8Effect p imm)) :=
  sub_al_imm8_triple_of_bytes p imm

attribute [x86_compose] subAlImm8Effect

@[x86_local] theorem subAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} :
    Effect.Local (subAlImm8Effect p imm8) := by
  effect_local [subAlImm8Effect]

end X86Proofs
