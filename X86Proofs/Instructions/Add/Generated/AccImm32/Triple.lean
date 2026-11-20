import X86Proofs.Instructions.Add.Generated.AccImm32.Step
import X86Proofs.Instructions.Add.Generated.AccImm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def addRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a + b⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

@[simp] theorem addRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (addRaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem addRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (addRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem add_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x05 :: immBytes 32 imm))
      (addRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), add_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x05 :: immBytes 32 imm))
      (Effect.post (addRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => addRaxImm32Effect_avoids p _ s _)
    (add_rax_imm32_effect_step p rex imm hrex)

theorem add_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAddRaxImm32 imm)) (Effect.post (addRaxImm32Effect p imm)) :=
  add_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def addEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a + b).setWidth 64⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

@[simp] theorem addEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (addEaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem addEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (addEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem add_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x05 :: immBytes 32 imm))
      (addEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), add_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x05 :: immBytes 32 imm))
      (Effect.post (addEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => addEaxImm32Effect_avoids p _ s _)
    (add_eax_imm32_effect_step p imm)

theorem add_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAddEaxImm32 imm)) (Effect.post (addEaxImm32Effect p imm)) :=
  add_eax_imm32_triple_of_bytes p imm

def addAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a + b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

@[simp] theorem addAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (addAxImm16Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem addAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (addAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem add_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x05 :: immBytes 16 imm))
      (addAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, add_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), add_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x05 :: immBytes 16 imm))
      (Effect.post (addAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => addAxImm16Effect_avoids p _ s _)
    (add_ax_imm16_effect_step p imm)

theorem add_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAddAxImm16 imm)) (Effect.post (addAxImm16Effect p imm)) :=
  add_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] addRaxImm32Effect addEaxImm32Effect addAxImm16Effect

@[x86_local] theorem addRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (addRaxImm32Effect p imm32) := by
  effect_local [addRaxImm32Effect]

@[x86_local] theorem addEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (addEaxImm32Effect p imm32) := by
  effect_local [addEaxImm32Effect]

@[x86_local] theorem addAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (addAxImm16Effect p imm16) := by
  effect_local [addAxImm16Effect]

end X86Proofs
