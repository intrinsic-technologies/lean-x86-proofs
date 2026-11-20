import X86Proofs.Instructions.Or.Generated.AccImm8.Step
import X86Proofs.Instructions.Or.Generated.AccImm8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Or.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def orAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (a ||| b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (orFlags (a ||| b)) }

@[simp] theorem orAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (s : RamState) :
    (orAlImm8Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem orAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (orAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem or_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x0C :: immBytes 8 imm))
      (orAlImm8Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, or_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), or_al_imm8_ready h imm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0x0C :: immBytes 8 imm))
      (Effect.post (orAlImm8Effect p imm)) :=
  Triple.of_effect (fun s _ => orAlImm8Effect_avoids p _ s _)
    (or_al_imm8_effect_step p imm)

theorem or_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrAlImm8 imm)) (Effect.post (orAlImm8Effect p imm)) :=
  or_al_imm8_triple_of_bytes p imm

attribute [x86_compose] orAlImm8Effect

@[x86_local] theorem orAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} :
    Effect.Local (orAlImm8Effect p imm8) := by
  effect_local [orAlImm8Effect]

end X86Proofs
