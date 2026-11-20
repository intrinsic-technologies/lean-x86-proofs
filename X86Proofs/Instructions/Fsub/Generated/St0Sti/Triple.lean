
import X86Proofs.Instructions.Fsub.Generated.St0Sti.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fsubSt0StiEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len
      [(top,
      (x87Arith .sub ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)
      ((Operand.fpr (top + i) : Operand 80).read s)).1)]
    (ftwSet ((Operand.ftw : Operand 16).read s) (top)
        (x87Tag
        (x87Arith .sub ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Arith .sub ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).2.2) (2)
        (ccC1
        (x87Arith .sub ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).2.1) s

@[simp] theorem fsubSt0StiEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (s : RamState) :
    (fsubSt0StiEffect p len top i s).components = [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] :=
        rfl

theorem fsub_st0_sti_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87ArithOk .sub s.FP87_Control s.FP87[fprIndex (top)]
        s.FP87[fprIndex (top + i)])
      (codeRange p [0xD8, modrmRegs 4 i]) (fsubSt0StiEffect p 2 top i) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hsrc, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fsub_st0_sti_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl
      (modrmRegs 4 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0
        (by simpa only [modrmRm_modrmRegs] using hsrc) (by simpa only [modrmRm_modrmRegs] using hok)
        hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fsubSt0StiEffect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status)
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).1)
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).1))
      (fun t => x87ArithFsw (t.FP87_Status) t.FP87_Status t.oracle
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).2.1
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).2.2) _ _ _ _
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
        simp only [Operand.read_fsw, fswRest_x87ArithFsw]
        rfl)
      (by
        exact fswCC_x87ArithFsw _ _ _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fsub_st0_sti_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87ArithOk .sub s.FP87_Control s.FP87[fprIndex (top)]
        s.FP87[fprIndex (top + i)])
      (codeRange p [0xD8, modrmRegs 4 i]) (Effect.post (fsubSt0StiEffect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fsubSt0StiEffect_components]; simp [Component.Covers]) _)
    (fsub_st0_sti_effect_step p top i)

attribute [x86_compose] fsubSt0StiEffect

@[x86_local] theorem fsubSt0StiEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} :
    Effect.Local (fsubSt0StiEffect p len top i) := by
  effect_local [fsubSt0StiEffect, x87Effect]

end X86Proofs
