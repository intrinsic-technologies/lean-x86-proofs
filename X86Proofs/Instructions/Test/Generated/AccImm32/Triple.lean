import X86Proofs.Instructions.Test.Generated.AccImm32.Step
import X86Proofs.Instructions.Test.Generated.AccImm32.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def testRaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 6
    writes := []
    flags := some (testFlags (a &&& b)) }

@[simp] theorem testRaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (testRaxImm32Effect p imm s).components = [.flags, .rip] := rfl

theorem testRaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (testRaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem test_rax_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xA9 :: immBytes 32 imm))
      (testRaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_rax_imm32_step s h rex imm hrex hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_rax_imm32_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 6 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 6 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_rax_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xA9 :: immBytes 32 imm))
      (Effect.post (testRaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => testRaxImm32Effect_avoids p _ s _)
    (test_rax_imm32_effect_step p rex imm hrex)

theorem test_rax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestRaxImm32 imm)) (Effect.post (testRaxImm32Effect p imm)) :=
  test_rax_imm32_triple_of_bytes p 0x48 imm (by unfold RexWPrefix; decide)

def testEaxImm32Effect (p : BitVec 64) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + 5
    writes := []
    flags := some (testFlags (a &&& b)) }

@[simp] theorem testEaxImm32Effect_components (p : BitVec 64) (imm : BitVec 32)
    (s : RamState) :
    (testEaxImm32Effect p imm s).components = [.flags, .rip] := rfl

theorem testEaxImm32Effect_avoids (p : BitVec 64) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (testEaxImm32Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem test_eax_imm32_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xA9 :: immBytes 32 imm))
      (testEaxImm32Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_eax_imm32_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_eax_imm32_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 5 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 5 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_eax_imm32_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (0xA9 :: immBytes 32 imm))
      (Effect.post (testEaxImm32Effect p imm)) :=
  Triple.of_effect (fun s _ => testEaxImm32Effect_avoids p _ s _)
    (test_eax_imm32_effect_step p imm)

theorem test_eax_imm32_triple [Bindings] (p : BitVec 64) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestEaxImm32 imm)) (Effect.post (testEaxImm32Effect p imm)) :=
  test_eax_imm32_triple_of_bytes p imm

def testAxImm16Effect (p : BitVec 64) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + 4
    writes := []
    flags := some (testFlags (a &&& b)) }

@[simp] theorem testAxImm16Effect_components (p : BitVec 64) (imm : BitVec 16)
    (s : RamState) :
    (testAxImm16Effect p imm s).components = [.flags, .rip] := rfl

theorem testAxImm16Effect_avoids (p : BitVec 64) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (testAxImm16Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem test_ax_imm16_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0xA9 :: immBytes 16 imm))
      (testAxImm16Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_ax_imm16_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_ax_imm16_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 4 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 4 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_ax_imm16_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0xA9 :: immBytes 16 imm))
      (Effect.post (testAxImm16Effect p imm)) :=
  Triple.of_effect (fun s _ => testAxImm16Effect_avoids p _ s _)
    (test_ax_imm16_effect_step p imm)

theorem test_ax_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestAxImm16 imm)) (Effect.post (testAxImm16Effect p imm)) :=
  test_ax_imm16_triple_of_bytes p imm

attribute [x86_compose] testRaxImm32Effect testEaxImm32Effect testAxImm16Effect

@[x86_local] theorem testRaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (testRaxImm32Effect p imm32) := by
  effect_local [testRaxImm32Effect]

@[x86_local] theorem testEaxImm32Effect_local {p : BitVec 64} {imm32 : BitVec 32} :
    Effect.Local (testEaxImm32Effect p imm32) := by
  effect_local [testEaxImm32Effect]

@[x86_local] theorem testAxImm16Effect_local {p : BitVec 64} {imm16 : BitVec 16} :
    Effect.Local (testAxImm16Effect p imm16) := by
  effect_local [testAxImm16Effect]

end X86Proofs
