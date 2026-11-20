
import X86Proofs.Instructions.Ffree.Generated.St.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def ffreeStEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len []
    (ftwSet ((Operand.ftw : Operand 16).read s) (top + i) 3)
    (((Operand.fsw : Operand 16).read s)) (2) (0) s

@[simp] theorem ffreeStEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3)
    (s : RamState) :
    (ffreeStEffect p len top i s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem ffree_st_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect (fun s => X87Pre p top s)
      (codeRange p [0xDD, modrmRegs 0 i]) (ffreeStEffect p 2 top i) := by
  rintro s h hcode ⟨hp, hcr0, hes, _, hfdp, htop⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := ffree_st_step s h hcr0 hes hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 0 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (ffreeStEffect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => t.FP87)
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status + i) 3)
      (fun t => fswC1Zero t.FP87_Status t.oracle) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswC1Zero]
        rfl)
      (by
        exact fswCC_fswC1Zero _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem ffree_st_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple (fun s => X87Pre p top s)
      (codeRange p [0xDD, modrmRegs 0 i]) (Effect.post (ffreeStEffect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ffreeStEffect_components]; simp [Component.Covers]) _)
    (ffree_st_effect_step p top i)

attribute [x86_compose] ffreeStEffect

@[x86_local] theorem ffreeStEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} {i : BitVec 3}
    :
    Effect.Local (ffreeStEffect p len top i) := by
  effect_local [ffreeStEffect, x87Effect]

end X86Proofs
