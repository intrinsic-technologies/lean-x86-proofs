import X86Proofs.Instructions.Or.Generated.AccImm32.Step
import X86Proofs.Instructions.Or.Generated.AccImm32.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Or.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def orRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a ||| b⟩]
    flags := some (orFlags (a ||| b)) }

@[simp] theorem orRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (orRaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem orRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (orRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem or_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x0D :: immBytes 32 imm))
      (orRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, or_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), or_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x0D :: immBytes 32 imm))
      (Effect.post (orRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => orRaxImm32Effect_avoids p _ s _)
    (or_rax_imm32_effect_step p rex imm hrex)

theorem or_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrRaxImm32 imm)) (Effect.post (orRaxImm32Effect p imm)) :=
  or_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def orEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a ||| b).setWidth 64⟩]
    flags := some (orFlags (a ||| b)) }

@[simp] theorem orEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (orEaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem orEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (orEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem or_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x0D :: immBytes 32 imm))
      (orEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, or_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), or_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x0D :: immBytes 32 imm))
      (Effect.post (orEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => orEaxImm32Effect_avoids p _ s _)
    (or_eax_imm32_effect_step p imm)

theorem or_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrEaxImm32 imm)) (Effect.post (orEaxImm32Effect p imm)) :=
  or_eax_imm32_triple_of_bytes p imm

def orAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a ||| b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (orFlags (a ||| b)) }

@[simp] theorem orAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (orAxImm16Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem orAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (orAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem or_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x0D :: immBytes 16 imm))
      (orAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, or_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), or_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem or_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x0D :: immBytes 16 imm))
      (Effect.post (orAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => orAxImm16Effect_avoids p _ s _)
    (or_ax_imm16_effect_step p imm)

theorem or_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeOrAxImm16 imm)) (Effect.post (orAxImm16Effect p imm)) :=
  or_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] orRaxImm32Effect orEaxImm32Effect orAxImm16Effect

@[x86_local] theorem orRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (orRaxImm32Effect p imm32) := by
  effect_local [orRaxImm32Effect]

@[x86_local] theorem orEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (orEaxImm32Effect p imm32) := by
  effect_local [orEaxImm32Effect]

@[x86_local] theorem orAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (orAxImm16Effect p imm16) := by
  effect_local [orAxImm16Effect]

end X86Proofs
