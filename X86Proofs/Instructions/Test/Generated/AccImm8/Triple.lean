import X86Proofs.Instructions.Test.Generated.AccImm8.Step
import X86Proofs.Instructions.Test.Generated.AccImm8.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def testAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 8).read s
  let b := imm.signExtend 8
  { rip := p + 2
    writes := []
    flags := some (testFlags (a &&& b)) }

@[simp] theorem testAlImm8Effect_components (p : BitVec 64) (imm : BitVec 8)
    (s : RamState) :
    (testAlImm8Effect p imm s).components = [.flags, .rip] := rfl

theorem testAlImm8Effect_avoids (p : BitVec 64) (imm : BitVec 8) (s : RamState)
    (code : CodeMap) : (testAlImm8Effect p imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem test_al_imm8_effect_step [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xA8 :: immBytes 8 imm))
      (testAlImm8Effect p imm) := by
  rintro s h hcode rfl
  refine ⟨_, test_al_imm8_step s h imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), test_al_imm8_ready h imm,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 1 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 1 _⟩⟩
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem test_al_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (0xA8 :: immBytes 8 imm))
      (Effect.post (testAlImm8Effect p imm)) :=
  Triple.of_effect (fun s _ => testAlImm8Effect_avoids p _ s _)
    (test_al_imm8_effect_step p imm)

theorem test_al_imm8_triple [Bindings] (p : BitVec 64) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeTestAlImm8 imm)) (Effect.post (testAlImm8Effect p imm)) :=
  test_al_imm8_triple_of_bytes p imm

attribute [x86_compose] testAlImm8Effect

@[x86_local] theorem testAlImm8Effect_local {p : BitVec 64} {imm8 : BitVec 8} :
    Effect.Local (testAlImm8Effect p imm8) := by
  effect_local [testAlImm8Effect]

end X86Proofs
