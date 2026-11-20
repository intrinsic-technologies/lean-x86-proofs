import X86Proofs.Instructions.Cmp.Generated.AccImm32.Step
import X86Proofs.Instructions.Cmp.Generated.AccImm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (cmpRaxImm32Effect p imm s).components = [.flags, .rip] := rfl

theorem cmpRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (cmpRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x3D :: immBytes 32 imm))
      (cmpRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_rax_imm32_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 6 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 6 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x3D :: immBytes 32 imm))
      (Effect.post (cmpRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => cmpRaxImm32Effect_avoids p _ s _)
    (cmp_rax_imm32_effect_step p rex imm hrex)

theorem cmp_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpRaxImm32 imm)) (Effect.post (cmpRaxImm32Effect p imm)) :=
  cmp_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def cmpEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (cmpEaxImm32Effect p imm s).components = [.flags, .rip] := rfl

theorem cmpEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (cmpEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x3D :: immBytes 32 imm))
      (cmpEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_eax_imm32_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 5 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 5 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x3D :: immBytes 32 imm))
      (Effect.post (cmpEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => cmpEaxImm32Effect_avoids p _ s _)
    (cmp_eax_imm32_effect_step p imm)

theorem cmp_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpEaxImm32 imm)) (Effect.post (cmpEaxImm32Effect p imm)) :=
  cmp_eax_imm32_triple_of_bytes p imm

def cmpAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (cmpAxImm16Effect p imm s).components = [.flags, .rip] := rfl

theorem cmpAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (cmpAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x3D :: immBytes 16 imm))
      (cmpAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_ax_imm16_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 4 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x3D :: immBytes 16 imm))
      (Effect.post (cmpAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => cmpAxImm16Effect_avoids p _ s _)
    (cmp_ax_imm16_effect_step p imm)

theorem cmp_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpAxImm16 imm)) (Effect.post (cmpAxImm16Effect p imm)) :=
  cmp_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] cmpRaxImm32Effect cmpEaxImm32Effect cmpAxImm16Effect

@[x86_local] theorem cmpRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (cmpRaxImm32Effect p imm32) := by
  effect_local [cmpRaxImm32Effect]

@[x86_local] theorem cmpEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (cmpEaxImm32Effect p imm32) := by
  effect_local [cmpEaxImm32Effect]

@[x86_local] theorem cmpAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (cmpAxImm16Effect p imm16) := by
  effect_local [cmpAxImm16Effect]

end X86Proofs
