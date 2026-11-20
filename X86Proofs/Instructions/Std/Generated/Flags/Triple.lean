
import X86Proofs.Instructions.Std.Generated.Flags.Step
import X86Proofs.Program.ReadWrite.Rflags
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def stdEffect (p : BitVec 64) (len : Nat) (_s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.df : Operand 1), stdSpec⟩] }

@[simp] theorem stdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (stdEffect p len s).components = [.df, .rip] := rfl

theorem std_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xFD]) (stdEffect p 1) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := std_step s h [] (by simp) (by simp) rfl rfl hcode.bytesAt hlow
  exact ⟨_, hstep, ReadyToStep.afterStep_writeResult_df h _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, Operand.read_afterStep_writeResult_df s _ _ _, trivial,
      AgreesExcept.afterStep_writeResult_df s _ _ _⟩⟩

theorem std_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0xFD]) (Effect.post (stdEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [stdEffect_components]; simp [Component.Covers]) _)
    (std_effect_step p)

attribute [x86_compose] stdEffect

@[x86_local] theorem stdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (stdEffect p len) := by
  effect_local [stdEffect, stdSpec]

end X86Proofs
