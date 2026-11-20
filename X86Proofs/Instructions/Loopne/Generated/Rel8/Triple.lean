import X86Proofs.Instructions.Loopne.Generated.Rel8.Step
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def loopneEffect (p : BitVec 64) (len : Nat) (disp : BitVec 8) (zf : Bool) (s : RamState) : Effect :=
  { rip := if loopTaken .LOOPNE (rcx.read s - 1) zf then
      branchTarget p len (disp.signExtend 64) else p + BitVec.ofNat 64 len
    writes := [⟨rcx, rcx.read s - 1⟩] }

@[simp] theorem loopneEffect_components (p : BitVec 64) (len : Nat) (disp : BitVec 8) (zf : Bool)
    (s : RamState) : (loopneEffect p len disp zf s).components = [.reg 1, .rip] := rfl

abbrev LoopnePre (p : BitVec 64) (disp : BitVec 8) (zf : Bool) (s : RamState) : Prop :=
  s.RIP = p ∧ (loopTaken .LOOPNE (rcx.read s - 1) zf = true →
    (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32) ∧
    (StatusFlags.ofRFLAGS s.RFLAGS).ZF = zf

theorem loopne_rel8_effect_step [Bindings] (hp5 : Bindings.processor.config.MODEP5 = false)
    (p : BitVec 64) (disp : BitVec 8) (zf : Bool) :
    StepEffect (LoopnePre p disp zf) (codeRange p (0xE0 :: immBytes 8 disp)) (loopneEffect p 2 disp zf) := by
  rintro s h hcode ⟨rfl, htarget, rfl⟩
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, loopne_rel8_step s h [] (by simp) (by simp) rfl rfl rfl hp5 disp hcode.bytesAt hlow
      htarget,
    ReadyToStep.afterStep_loop h _ _ _ _,
    ⟨afterStep_loop_rip h _ _ _ _, Operand.read_afterStep_loop_rcx _ _ _ _ _, trivial,
      AgreesExcept.afterStep_loop _ _ _ _ _⟩⟩

theorem loopne_rel8_triple [Bindings] (hp5 : Bindings.processor.config.MODEP5 = false)
    (p : BitVec 64) (disp : BitVec 8) (zf : Bool) :
    Triple (LoopnePre p disp zf) (codeRange p (0xE0 :: immBytes 8 disp))
      (Effect.post (loopneEffect p 2 disp zf)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [loopneEffect_components]; simp [Component.Covers]) _)
    (loopne_rel8_effect_step hp5 p disp zf)

attribute [x86_compose] loopneEffect

@[x86_local] theorem loopneEffect_local {p : BitVec 64} {len : Nat} {disp : BitVec 8} {zf : Bool} :
    Effect.Local (loopneEffect p len disp zf) := by
  effect_local [loopneEffect, loopTaken]

def loopneA32Effect (p : BitVec 64) (len : Nat) (disp : BitVec 8) (zf : Bool) (s : RamState) : Effect :=
  { rip := if loopTaken .LOOPNE (loopCount32 s) zf then
      branchTarget p len (disp.signExtend 64) else p + BitVec.ofNat 64 len
    writes := [⟨rcx, loopCount32 s⟩] }

@[simp] theorem loopneA32Effect_components (p : BitVec 64) (len : Nat) (disp : BitVec 8) (zf : Bool)
    (s : RamState) : (loopneA32Effect p len disp zf s).components = [.reg 1, .rip] := rfl

abbrev LoopneA32Pre (p : BitVec 64) (disp : BitVec 8) (zf : Bool) (s : RamState) : Prop :=
  s.RIP = p ∧ (loopTaken .LOOPNE (loopCount32 s) zf = true →
    (branchTarget p 3 (disp.signExtend 64)).toNat < 2^32) ∧
    (StatusFlags.ofRFLAGS s.RFLAGS).ZF = zf

theorem loopne_rel8_a32_effect_step [Bindings] (hp5 : Bindings.processor.config.MODEP5 = false)
    (p : BitVec 64) (disp : BitVec 8) (zf : Bool) :
    StepEffect (LoopneA32Pre p disp zf) (codeRange p (0x67 :: 0xE0 :: immBytes 8 disp))
      (loopneA32Effect p 3 disp zf) := by
  rintro s h hcode ⟨rfl, htarget, rfl⟩
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, loopne_rel8_a32_step s h [0x67] (by simp [scanPrefix_67]) (by simp) rfl rfl rfl hp5 disp
      hcode.bytesAt hlow htarget,
    ReadyToStep.afterStep_loop32 h _ _ _ _,
    ⟨afterStep_loop32_rip h _ _ _ _, Operand.read_afterStep_loop32_rcx _ _ _ _ _, trivial,
      AgreesExcept.afterStep_loop32 _ _ _ _ _⟩⟩

theorem loopne_rel8_a32_triple [Bindings] (hp5 : Bindings.processor.config.MODEP5 = false)
    (p : BitVec 64) (disp : BitVec 8) (zf : Bool) :
    Triple (LoopneA32Pre p disp zf) (codeRange p (0x67 :: 0xE0 :: immBytes 8 disp))
      (Effect.post (loopneA32Effect p 3 disp zf)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [loopneA32Effect_components]; simp [Component.Covers]) _)
    (loopne_rel8_a32_effect_step hp5 p disp zf)

attribute [x86_compose] loopneA32Effect

@[x86_local] theorem loopneA32Effect_local {p : BitVec 64} {len : Nat} {disp : BitVec 8} {zf : Bool} :
    Effect.Local (loopneA32Effect p len disp zf) := by
  effect_local [loopneA32Effect, loopTaken, loopCount32]

end X86Proofs
