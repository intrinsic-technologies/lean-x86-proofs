import X86Proofs.Instructions.Jrcxz.Generated.Rel8.Step
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def jrcxzEffect (p : BitVec 64) (len : Nat) (disp : BitVec 8) (s : RamState) : Effect :=
  branchEffect (rcx.read s == 0#64) (p + BitVec.ofNat 64 len)
    (branchTarget p len (disp.signExtend 64))

@[simp] theorem jrcxzEffect_components (p : BitVec 64) (len : Nat) (disp : BitVec 8) (s : RamState) :
    (jrcxzEffect p len disp s).components = [.rip] := rfl

abbrev JrcxzPre (p : BitVec 64) (disp : BitVec 8) (s : RamState) : Prop :=
  s.RIP = p ∧ (rcx.read s = 0#64 → (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32)

theorem jrcxz_rel8_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 8) :
    StepEffect (JrcxzPre p disp) (codeRange p (0xE3 :: immBytes 8 disp)) (jrcxzEffect p 2 disp) := by
  rintro s h hcode ⟨rfl, htarget⟩
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, jrcxz_rel8_step s h [] (by simp) (by simp) rfl rfl rfl disp hcode.bytesAt hlow
      htarget,
    ReadyToStep.afterStep_branchState h _ _ _ _, branchEffect_holds h _ _ _ _⟩

theorem jrcxz_rel8_triple [Bindings] (p : BitVec 64) (disp : BitVec 8) :
    Triple (JrcxzPre p disp) (codeRange p (0xE3 :: immBytes 8 disp)) (Effect.post (jrcxzEffect p 2 disp)) :=
  Triple.of_effect (fun _ _ => branchEffect_avoids _ _ _ _) (jrcxz_rel8_effect_step p disp)

attribute [x86_compose] jrcxzEffect

@[x86_local] theorem jrcxzEffect_local {p : BitVec 64} {len : Nat} {disp : BitVec 8} :
    Effect.Local (jrcxzEffect p len disp) := by
  effect_local [jrcxzEffect, branchEffect]

def jecxzEffect (p : BitVec 64) (len : Nat) (disp : BitVec 8) (s : RamState) : Effect :=
  branchEffect ((rcx.read s).setWidth 32 == 0#32) (p + BitVec.ofNat 64 len)
    (branchTarget p len (disp.signExtend 64))

@[simp] theorem jecxzEffect_components (p : BitVec 64) (len : Nat) (disp : BitVec 8) (s : RamState) :
    (jecxzEffect p len disp s).components = [.rip] := rfl

abbrev JecxzPre (p : BitVec 64) (disp : BitVec 8) (s : RamState) : Prop :=
  s.RIP = p ∧ ((rcx.read s).setWidth 32 = 0#32 →
    (branchTarget p 3 (disp.signExtend 64)).toNat < 2^32)

theorem jecxz_rel8_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 8) :
    StepEffect (JecxzPre p disp) (codeRange p (0x67 :: 0xE3 :: immBytes 8 disp)) (jecxzEffect p 3 disp) := by
  rintro s h hcode ⟨rfl, htarget⟩
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, jecxz_rel8_step s h [0x67] (by simp [scanPrefix_67]) (by simp) rfl rfl rfl disp
      hcode.bytesAt hlow htarget,
    ReadyToStep.afterStep_branchState h _ _ _ _, branchEffect_holds h _ _ _ _⟩

theorem jecxz_rel8_triple [Bindings] (p : BitVec 64) (disp : BitVec 8) :
    Triple (JecxzPre p disp) (codeRange p (0x67 :: 0xE3 :: immBytes 8 disp)) (Effect.post (jecxzEffect p 3 disp)) :=
  Triple.of_effect (fun _ _ => branchEffect_avoids _ _ _ _) (jecxz_rel8_effect_step p disp)

attribute [x86_compose] jecxzEffect

@[x86_local] theorem jecxzEffect_local {p : BitVec 64} {len : Nat} {disp : BitVec 8} :
    Effect.Local (jecxzEffect p len disp) := by
  effect_local [jecxzEffect, branchEffect]

end X86Proofs
