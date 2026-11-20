import X86Proofs.Instructions.Sub.Generated.AccImm32.Step
import X86Proofs.Instructions.Sub.Generated.AccImm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def subRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a - b⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (subRaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem subRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (subRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x2D :: immBytes 32 imm))
      (subRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x2D :: immBytes 32 imm))
      (Effect.post (subRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => subRaxImm32Effect_avoids p _ s _)
    (sub_rax_imm32_effect_step p rex imm hrex)

theorem sub_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubRaxImm32 imm)) (Effect.post (subRaxImm32Effect p imm)) :=
  sub_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def subEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a - b).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (subEaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem subEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (subEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x2D :: immBytes 32 imm))
      (subEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x2D :: immBytes 32 imm))
      (Effect.post (subEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => subEaxImm32Effect_avoids p _ s _)
    (sub_eax_imm32_effect_step p imm)

theorem sub_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubEaxImm32 imm)) (Effect.post (subEaxImm32Effect p imm)) :=
  sub_eax_imm32_triple_of_bytes p imm

def subAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a - b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (subAxImm16Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem subAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (subAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x2D :: immBytes 16 imm))
      (subAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x2D :: immBytes 16 imm))
      (Effect.post (subAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => subAxImm16Effect_avoids p _ s _)
    (sub_ax_imm16_effect_step p imm)

theorem sub_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubAxImm16 imm)) (Effect.post (subAxImm16Effect p imm)) :=
  sub_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] subRaxImm32Effect subEaxImm32Effect subAxImm16Effect

@[x86_local] theorem subRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (subRaxImm32Effect p imm32) := by
  effect_local [subRaxImm32Effect]

@[x86_local] theorem subEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (subEaxImm32Effect p imm32) := by
  effect_local [subEaxImm32Effect]

@[x86_local] theorem subAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (subAxImm16Effect p imm16) := by
  effect_local [subAxImm16Effect]

end X86Proofs
