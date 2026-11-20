import X86Proofs.Instructions.Sbb.Generated.AccImm32.Step
import X86Proofs.Instructions.Sbb.Generated.AccImm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def sbbRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a - (b + BitVec.ofNat 64 c.toNat)⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) :
    (sbbRaxImm32Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem sbbRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbRaxImm32Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x1D :: immBytes 32 imm))
      (sbbRaxImm32Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (c : Bool) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (rex :: 0x1D :: immBytes 32 imm))
      (Effect.post (sbbRaxImm32Effect p imm c)) :=
  Triple.of_effect (fun s _ => sbbRaxImm32Effect_avoids p _ _ s _)
    (sbb_rax_imm32_effect_step p rex imm c hrex)

theorem sbb_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbRaxImm32 imm)) (Effect.post (sbbRaxImm32Effect p imm c)) :=
  sbb_rax_imm32_triple_of_bytes p 0x48 imm c (by unfold RexWPrefix; decide)

def sbbEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a - (b + BitVec.ofNat 32 c.toNat)).setWidth 64⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) :
    (sbbEaxImm32Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem sbbEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbEaxImm32Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x1D :: immBytes 32 imm))
      (sbbEaxImm32Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x1D :: immBytes 32 imm))
      (Effect.post (sbbEaxImm32Effect p imm c)) :=
  Triple.of_effect (fun s _ => sbbEaxImm32Effect_avoids p _ _ s _)
    (sbb_eax_imm32_effect_step p imm c)

theorem sbb_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbEaxImm32 imm)) (Effect.post (sbbEaxImm32Effect p imm c)) :=
  sbb_eax_imm32_triple_of_bytes p imm c

def sbbAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a - (b + BitVec.ofNat 16 c.toNat)) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (sbbSpec c a b).2) }

@[simp] theorem sbbAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (c : Bool) (s : RamState) :
    (sbbAxImm16Effect p imm c s).components = [.reg 0, .flags, .rip] := rfl

theorem sbbAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16)
    (c : Bool) (s : RamState) (code : CodeMap) : (sbbAxImm16Effect p imm c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sbb_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x1D :: immBytes 16 imm))
      (sbbAxImm16Effect p imm c) := by
  rintro s h hcode ⟨rfl, rfl⟩
  refine ⟨_, sbb_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sbb_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, sbbSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch, afterFetches_RFLAGS, beforeFetch_RFLAGS]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sbb_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (0x66 :: 0x1D :: immBytes 16 imm))
      (Effect.post (sbbAxImm16Effect p imm c)) :=
  Triple.of_effect (fun s _ => sbbAxImm16Effect_avoids p _ _ s _)
    (sbb_ax_imm16_effect_step p imm c)

theorem sbb_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ (StatusFlags.ofRFLAGS s.RFLAGS).CF = c)
      (codeRange p (encodeSbbAxImm16 imm)) (Effect.post (sbbAxImm16Effect p imm c)) :=
  sbb_ax_imm16_triple_of_bytes p imm c

attribute [x86_compose] sbbRaxImm32Effect sbbEaxImm32Effect sbbAxImm16Effect

@[x86_local] theorem sbbRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (sbbRaxImm32Effect p imm32 c) := by
  effect_local [sbbRaxImm32Effect]

@[x86_local] theorem sbbEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} {c : Bool} :
    Effect.Local (sbbEaxImm32Effect p imm32 c) := by
  effect_local [sbbEaxImm32Effect]

@[x86_local] theorem sbbAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} {c : Bool} :
    Effect.Local (sbbAxImm16Effect p imm16 c) := by
  effect_local [sbbAxImm16Effect]

end X86Proofs
