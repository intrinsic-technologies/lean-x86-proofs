import X86Proofs.Instructions.Cmp.Generated.AccImm8.Step
import X86Proofs.Instructions.Cmp.Generated.AccImm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (s : RamState) :
    (cmpAlImm8Effect p imm s).components = [.flags, .rip] := rfl

theorem cmpAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (cmpAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x3C :: immBytes 8 imm))
      (cmpAlImm8Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_al_imm8_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0x3C :: immBytes 8 imm))
      (Effect.post (cmpAlImm8Effect p imm)) :=
  Triple.of_effect (fun s _ => cmpAlImm8Effect_avoids p _ s _)
    (cmp_al_imm8_effect_step p imm)

theorem cmp_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpAlImm8 imm)) (Effect.post (cmpAlImm8Effect p imm)) :=
  cmp_al_imm8_triple_of_bytes p imm

attribute [x86_compose] cmpAlImm8Effect

@[x86_local] theorem cmpAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} :
    Effect.Local (cmpAlImm8Effect p imm8) := by
  effect_local [cmpAlImm8Effect]

end X86Proofs
