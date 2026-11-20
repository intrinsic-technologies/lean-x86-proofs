import X86Proofs.Instructions.Xor.Generated.AccImm32.Step
import X86Proofs.Instructions.Xor.Generated.AccImm32.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Xor.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xorRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := [⟨(Operand.reg 0 : Operand 64), a ^^^ b⟩]
    flags := some (xorFlags (a ^^^ b)) }

@[simp] theorem xorRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (xorRaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem xorRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (xorRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem xor_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x35 :: immBytes 32 imm))
      (xorRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, xor_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), xor_rax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x35 :: immBytes 32 imm))
      (Effect.post (xorRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => xorRaxImm32Effect_avoids p _ s _)
    (xor_rax_imm32_effect_step p rex imm hrex)

theorem xor_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXorRaxImm32 imm)) (Effect.post (xorRaxImm32Effect p imm)) :=
  xor_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def xorEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := [⟨(Operand.reg 0 : Operand 64), (a ^^^ b).setWidth 64⟩]
    flags := some (xorFlags (a ^^^ b)) }

@[simp] theorem xorEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (xorEaxImm32Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem xorEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (xorEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem xor_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x35 :: immBytes 32 imm))
      (xorEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, xor_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), xor_eax_imm32_ready h imm,
    ⟨afterStep_writeOutputs_rip h 5 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x35 :: immBytes 32 imm))
      (Effect.post (xorEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => xorEaxImm32Effect_avoids p _ s _)
    (xor_eax_imm32_effect_step p imm)

theorem xor_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXorEaxImm32 imm)) (Effect.post (xorEaxImm32Effect p imm)) :=
  xor_eax_imm32_triple_of_bytes p imm

def xorAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (a ^^^ b) ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (xorFlags (a ^^^ b)) }

@[simp] theorem xorAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (xorAxImm16Effect p imm s).components = [.reg 0, .flags, .rip] := rfl

theorem xorAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (xorAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem xor_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x35 :: immBytes 16 imm))
      (xorAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, xor_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), xor_ax_imm16_ready h imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x35 :: immBytes 16 imm))
      (Effect.post (xorAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => xorAxImm16Effect_avoids p _ s _)
    (xor_ax_imm16_effect_step p imm)

theorem xor_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXorAxImm16 imm)) (Effect.post (xorAxImm16Effect p imm)) :=
  xor_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] xorRaxImm32Effect xorEaxImm32Effect xorAxImm16Effect

@[x86_local] theorem xorRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (xorRaxImm32Effect p imm32) := by
  effect_local [xorRaxImm32Effect]

@[x86_local] theorem xorEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (xorEaxImm32Effect p imm32) := by
  effect_local [xorEaxImm32Effect]

@[x86_local] theorem xorAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (xorAxImm16Effect p imm16) := by
  effect_local [xorAxImm16Effect]

end X86Proofs
