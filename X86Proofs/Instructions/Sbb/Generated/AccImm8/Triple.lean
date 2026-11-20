import X86Proofs.Instructions.Sbb.Generated.AccImm8.Step
import X86Proofs.Instructions.Sbb.Generated.AccImm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def sbbAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (a - (b + BitVec.ofNat 8 c.toNat)) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (c : Bool) (s : RamState) :
    (sbbAlImm8Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem sbbAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbAlImm8Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x1C :: immBytes 8 imm))
      (sbbAlImm8Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_al_imm8_ready h imm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x1C :: immBytes 8 imm))
      (Effect.post (sbbAlImm8Effect p imm c)) :=
  Triple.of_effect (fun s _ => sbbAlImm8Effect_avoids p _ _ s _)
    (sbb_al_imm8_effect_step p imm c)

theorem sbb_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbAlImm8 imm)) (Effect.post (sbbAlImm8Effect p imm c)) :=
  sbb_al_imm8_triple_of_bytes p imm c

attribute [x86_compose] sbbAlImm8Effect

@[x86_local] theorem sbbAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} {c : Bool} :
    Effect.Local (sbbAlImm8Effect p imm8 c) := by
  effect_local [sbbAlImm8Effect]

end X86Proofs
