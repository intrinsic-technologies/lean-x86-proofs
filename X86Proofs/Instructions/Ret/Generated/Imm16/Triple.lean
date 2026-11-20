import X86Proofs.Instructions.Ret.Generated.Imm16.Step
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def retImm16Effect (imm : BitVec 16) (s : RamState) : Effect where
  rip := stackTop s
  writes := [⟨(Operand.reg 4 : Operand 64), stackPtr s + 8 + imm.setWidth 64⟩]

@[simp] theorem retImm16Effect_components (imm : BitVec 16) (s : RamState) :
    (retImm16Effect imm s).components = [.reg 4, .rip] := rfl

theorem ret_imm16_effect_step [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    StepEffect (RetPre p) (codeRange p (0xC2 :: immBytes 16 imm)) (retImm16Effect imm) := by
  rintro s h hcode ⟨hpre, htarget⟩
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, ret_imm16_step s h [] (by simp) (by simp) rfl rfl rfl imm hcode.bytesAt hlow
      hpre.read htarget,
    ReadyToStep.afterStep_retImm h _ _ _,
    ⟨afterStep_retImm_rip _ _ _, Operand.read_afterStep_retImm_rsp _ _ _ _, trivial,
      AgreesExcept.afterStep_retImm _ _ _ _⟩⟩

theorem ret_imm16_triple [Bindings] (p : BitVec 64) (imm : BitVec 16) :
    Triple (RetPre p) (codeRange p (0xC2 :: immBytes 16 imm)) (Effect.post (retImm16Effect imm)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (retImm16Effect_components imm s) _)
    (ret_imm16_effect_step p imm)

attribute [x86_compose] retImm16Effect

@[x86_local] theorem retImm16Effect_local {imm : BitVec 16} : Effect.Local (retImm16Effect imm) := by
  effect_local [retImm16Effect, stackTop, stackPtr]

end X86Proofs
