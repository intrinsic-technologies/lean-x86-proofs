
import X86Proofs.Instructions.Xlat.Generated.Table.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xlatEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64),
    mergeGPR 8 ((Operand.mem (xlatAddr s) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩]

@[simp] theorem xlatEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (xlatEffect p len s).components = [.reg 0, .rip] := rfl

abbrev XlatPre (p : BitVec 64) : RamState → Prop :=
  LoadPre p xlatAddr 1

theorem xlat_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (XlatPre p) (codeRange p [0xD7]) (xlatEffect p 1) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, xlat_step s h [] (by simp) (by simp) rfl rfl rfl rfl rfl hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_xlat h _ _,
    ⟨afterStep_xlat_rip h _ _, Operand.read_afterStep_xlat_rax _ _ _, trivial,
      AgreesExcept.afterStep_xlat _ _ _⟩⟩

theorem xlat_triple [Bindings] (p : BitVec 64) :
    Triple (XlatPre p) (codeRange p [0xD7]) (Effect.post (xlatEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xlatEffect_components]; simp [Component.Covers]) _)
    (xlat_effect_step p)

attribute [x86_compose] xlatEffect

@[x86_local] theorem xlatEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (xlatEffect p len) := by
  effect_local [xlatEffect, xlatAddr]

end X86Proofs
