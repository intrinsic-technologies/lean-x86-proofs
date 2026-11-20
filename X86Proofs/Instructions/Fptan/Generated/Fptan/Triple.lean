
import X86Proofs.Instructions.Fptan.Generated.Fptan.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fptanEffect [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len
      [(top, if
      (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
      ((Operand.fcw : Operand 16).read s)).2.2.2.1 then ((Operand.fpr (top) : Operand 80).read s)
      else
      (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
      ((Operand.fcw : Operand 16).read s)).2.1),
      (top - 1, if
      (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
      ((Operand.fcw : Operand 16).read s)).2.2.2.1 then
      ((Operand.fpr (top - 1) : Operand 80).read s) else
      (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
      ((Operand.fcw : Operand 16).read s)).1)]
    (if
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.2.1 then ((Operand.ftw : Operand 16).read s) else
        ftwSet
        (ftwSet ((Operand.ftw : Operand 16).read s) top
        (x87Tag
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.1)) (top - 1)
        (x87Tag
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).1))
    (if
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.2.1 then fswOrFlags
        ((Operand.fsw : Operand 16).read s)
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.2.2 else fswSetTop
        (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.2.2) (top - 1)) (6)
        (ccC1C2
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.1
        (x87BindVal (FP87.Tan ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.2.1) s

theorem fptanEffect_components [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (s : RamState) :
    (fptanEffect p len top s).components =
        [.fpr (top), .fpr (top - 1), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

attribute [simp] fptanEffect_components

theorem fptan_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 7) = 3 ∧ X87BindOk (FP87.Tan s.FP87[fprIndex (top)]) s.FP87_Control)
      (codeRange p [0xD9, 0xF2]) (fptanEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hpush, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fptan_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xF2 (by decide)
    (by decide) (by decide) h0 hpush hok hcode.bytesAt hlow
  have hh : (fptanEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 2) _
      (fun t => if
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.1
          then t.FP87 else fprSet
          (fprSet t.FP87 (fswTop t.FP87_Status)
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.1)
          (fswTop t.FP87_Status - 1)
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).1)
      (fun t => if
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.1
          then t.FP87_Tag_Word else ftwSet
          (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.1))
          (fswTop t.FP87_Status - 1)
          (x87Tag (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).1))
      (fun t => if
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.1
          then x87SinFsw t.FP87_Status t.oracle
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.1
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.2
          else fswSetTop
          (x87SinFsw t.FP87_Status t.oracle
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.1
          (x87BindVal (FP87.Tan t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2.2)
          (fswTop t.FP87_Status - 1)) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrv
        rcases hrv with rfl | rfl
        · exact fprSet2_ite_get_hi _ _ _ _ _
        · exact fprSet2_ite_get_lo _ _ _ _ _)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hr
        exact fprSet2_ite_get_of_ne _ _ (Ne.symm hr.1) (Ne.symm hr.2) _ _)
      (by
        simp only [Operand.read_ftw, Operand.read_fpr, Operand.read_fcw]
        rfl)
      (by
        simp only [Operand.read_fsw]
        exact fswRest_ite_setTop _ _ _ _ (fswRest_x87SinFsw _ _ _ _ _))
      (by
        rw [fswCC_ite_setTop]
        exact fswCC_x87SinFsw _ _ _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fptan_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 7) = 3 ∧ X87BindOk (FP87.Tan s.FP87[fprIndex (top)]) s.FP87_Control)
      (codeRange p [0xD9, 0xF2]) (Effect.post (fptanEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fptanEffect_components]; simp [Component.Covers]) _)
    (fptan_effect_step p top)

attribute [x86_compose] fptanEffect

@[x86_local] theorem fptanEffect_local [Bindings] {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fptanEffect p len top) := by
  effect_local [fptanEffect, x87Effect]

end X86Proofs
