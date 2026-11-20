
import X86Proofs.Instructions.Fst.Generated.St.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fstStEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len [(top + i, ((Operand.fpr (top) : Operand 80).read s))]
    (ftwSet ((Operand.ftw : Operand 16).read s) (top + i)
        (x87Tag ((Operand.fpr (top) : Operand 80).read s)))
    (((Operand.fsw : Operand 16).read s)) (2) (0) s

@[simp] theorem fstStEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3)
    (s : RamState) :
    (fstStEffect p len top i s).components = [.fpr (top + i), .ftw, .fsw, .fcc, .fpuPtr, .rip] :=
        rfl

theorem fst_st_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3)
      (codeRange p [0xDD, modrmRegs 2 i]) (fstStEffect p 2 top i) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fst_st_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 2 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0 hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fstStEffect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status + i) t.FP87[fprIndex (fswTop t.FP87_Status)])
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status + i)
          (x87Tag t.FP87[fprIndex (fswTop t.FP87_Status)]))
      (fun t => fstStatus t.FP87_Status t.oracle) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_singleton] at hrv
        subst hrv
        exact fprSet_get_self _ _ _)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        exact fprSet_get_of_ne _ (Ne.symm hr) _)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fstStatus]
        rfl)
      (by
        exact fswCC_fstStatus_c1 _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fst_st_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3)
      (codeRange p [0xDD, modrmRegs 2 i]) (Effect.post (fstStEffect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fstStEffect_components]; simp [Component.Covers]) _)
    (fst_st_effect_step p top i)

attribute [x86_compose] fstStEffect

@[x86_local] theorem fstStEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} {i : BitVec 3} :
    Effect.Local (fstStEffect p len top i) := by
  effect_local [fstStEffect, x87Effect]

end X86Proofs
