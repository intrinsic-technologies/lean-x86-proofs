import X86Proofs.Instructions.And.Generated.AccImm32.Step
import X86Proofs.Instructions.And.Generated.AccImm32.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.And.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def andRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a &&& b⟩]
    flags := some (andFlags (a &&& b)) }

@[simp] theorem andRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (andRaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem andRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (andRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem and_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x25 :: immBytes 32 imm))
      (andRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x25 :: immBytes 32 imm))
      (Effect.post (andRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => andRaxImm32Effect_avoids p _ s _)
    (and_rax_imm32_effect_step p rex imm hrex)

theorem and_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAndRaxImm32 imm)) (Effect.post (andRaxImm32Effect p imm)) :=
  and_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def andEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a &&& b).setWidth 64⟩]
    flags := some (andFlags (a &&& b)) }

@[simp] theorem andEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (andEaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem andEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (andEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem and_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x25 :: immBytes 32 imm))
      (andEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x25 :: immBytes 32 imm))
      (Effect.post (andEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => andEaxImm32Effect_avoids p _ s _)
    (and_eax_imm32_effect_step p imm)

theorem and_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAndEaxImm32 imm)) (Effect.post (andEaxImm32Effect p imm)) :=
  and_eax_imm32_triple_of_bytes p imm

def andAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a &&& b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (andFlags (a &&& b)) }

@[simp] theorem andAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (andAxImm16Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem andAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (andAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem and_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x25 :: immBytes 16 imm))
      (andAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, and_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), and_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x25 :: immBytes 16 imm))
      (Effect.post (andAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => andAxImm16Effect_avoids p _ s _)
    (and_ax_imm16_effect_step p imm)

theorem and_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeAndAxImm16 imm)) (Effect.post (andAxImm16Effect p imm)) :=
  and_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] andRaxImm32Effect andEaxImm32Effect andAxImm16Effect

@[x86_local] theorem andRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (andRaxImm32Effect p imm32) := by
  effect_local [andRaxImm32Effect]

@[x86_local] theorem andEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (andEaxImm32Effect p imm32) := by
  effect_local [andEaxImm32Effect]

@[x86_local] theorem andAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (andAxImm16Effect p imm16) := by
  effect_local [andAxImm16Effect]

end X86Proofs
