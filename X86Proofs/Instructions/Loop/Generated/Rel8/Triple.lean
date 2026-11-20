import X86Proofs.Instructions.Loop.Generated.Rel8.Step
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def loopEffect (p : BitVec 64) (len : Nat) (disp : BitVec 8) (s : RamState) : Effect :=
  { rip := if loopTaken .LOOP (rcx.read s - 1) false then
      branchTarget p len (disp.signExtend 64) else p + BitVec.ofNat 64 len
    writes := [⟨rcx, rcx.read s - 1⟩] }

@[simp] theorem loopEffect_components (p : BitVec 64) (len : Nat) (disp : BitVec 8)
    (s : RamState) : (loopEffect p len disp s).components = [.reg 1, .rip] := rfl

abbrev LoopPre (p : BitVec 64) (disp : BitVec 8) (s : RamState) : Prop :=
  s.RIP = p ∧ (loopTaken .LOOP (rcx.read s - 1) false = true →
    (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32)

theorem loop_rel8_effect_step [Bindings]
    (p : BitVec 64) (disp : BitVec 8) :
    StepEffect (LoopPre p disp) (codeRange p (0xE2 :: immBytes 8 disp)) (loopEffect p 2 disp) := by
  rintro s h hcode ⟨rfl, htarget⟩
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, loop_rel8_step s h [] (by simp) (by simp) rfl rfl rfl disp hcode.bytesAt hlow
      htarget,
    ReadyToStep.afterStep_loop h _ _ _ _,
    ⟨afterStep_loop_rip h _ _ _ _, Operand.read_afterStep_loop_rcx _ _ _ _ _, trivial,
      AgreesExcept.afterStep_loop _ _ _ _ _⟩⟩

theorem loop_rel8_triple [Bindings]
    (p : BitVec 64) (disp : BitVec 8) :
    Triple (LoopPre p disp) (codeRange p (0xE2 :: immBytes 8 disp))
      (Effect.post (loopEffect p 2 disp)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [loopEffect_components]; simp [Component.Covers]) _)
    (loop_rel8_effect_step p disp)

attribute [x86_compose] loopEffect

@[x86_local] theorem loopEffect_local {p : BitVec 64} {len : Nat} {disp : BitVec 8} :
    Effect.Local (loopEffect p len disp) := by
  effect_local [loopEffect, loopTaken]

def loopA32Effect (p : BitVec 64) (len : Nat) (disp : BitVec 8) (s : RamState) : Effect :=
  { rip := if loopTaken .LOOP (loopCount32 s) false then
      branchTarget p len (disp.signExtend 64) else p + BitVec.ofNat 64 len
    writes := [⟨rcx, loopCount32 s⟩] }

@[simp] theorem loopA32Effect_components (p : BitVec 64) (len : Nat) (disp : BitVec 8)
    (s : RamState) : (loopA32Effect p len disp s).components = [.reg 1, .rip] := rfl

abbrev LoopA32Pre (p : BitVec 64) (disp : BitVec 8) (s : RamState) : Prop :=
  s.RIP = p ∧ (loopTaken .LOOP (loopCount32 s) false = true →
    (branchTarget p 3 (disp.signExtend 64)).toNat < 2^32)

theorem loop_rel8_a32_effect_step [Bindings]
    (p : BitVec 64) (disp : BitVec 8) :
    StepEffect (LoopA32Pre p disp) (codeRange p (0x67 :: 0xE2 :: immBytes 8 disp))
      (loopA32Effect p 3 disp) := by
  rintro s h hcode ⟨rfl, htarget⟩
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, loop_rel8_a32_step s h [0x67] (by simp [scanPrefix_67]) (by simp) rfl rfl rfl disp
      hcode.bytesAt hlow htarget,
    ReadyToStep.afterStep_loop32 h _ _ _ _,
    ⟨afterStep_loop32_rip h _ _ _ _, Operand.read_afterStep_loop32_rcx _ _ _ _ _, trivial,
      AgreesExcept.afterStep_loop32 _ _ _ _ _⟩⟩

theorem loop_rel8_a32_triple [Bindings]
    (p : BitVec 64) (disp : BitVec 8) :
    Triple (LoopA32Pre p disp) (codeRange p (0x67 :: 0xE2 :: immBytes 8 disp))
      (Effect.post (loopA32Effect p 3 disp)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [loopA32Effect_components]; simp [Component.Covers]) _)
    (loop_rel8_a32_effect_step p disp)

attribute [x86_compose] loopA32Effect

@[x86_local] theorem loopA32Effect_local {p : BitVec 64} {len : Nat} {disp : BitVec 8} :
    Effect.Local (loopA32Effect p len disp) := by
  effect_local [loopA32Effect, loopTaken, loopCount32]

end X86Proofs
