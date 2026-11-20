import X86Proofs.Instructions.Add.Generated.AccImm8.Step
import X86Proofs.Instructions.Add.Generated.AccImm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def addAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (a + b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

@[simp] theorem addAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (s : RamState) :
    (addAlImm8Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem addAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (addAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem add_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x04 :: immBytes 8 imm))
      (addAlImm8Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), add_al_imm8_ready h imm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0x04 :: immBytes 8 imm))
      (Effect.post (addAlImm8Effect p imm)) :=
  Triple.of_effect (fun s _ => addAlImm8Effect_avoids p _ s _)
    (add_al_imm8_effect_step p imm)

theorem add_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAddAlImm8 imm)) (Effect.post (addAlImm8Effect p imm)) :=
  add_al_imm8_triple_of_bytes p imm

attribute [x86_compose] addAlImm8Effect

@[x86_local] theorem addAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} :
    Effect.Local (addAlImm8Effect p imm8) := by
  effect_local [addAlImm8Effect]

end X86Proofs
