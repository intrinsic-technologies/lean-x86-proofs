
import X86Proofs.Instructions.Fsin.Generated.Fsin.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fsinEffect [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len
      [(top, if
      (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
      ((Operand.fcw : Operand 16).read s)).2.2.1 then ((Operand.fpr (top) : Operand 80).read s) else
      (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
      ((Operand.fcw : Operand 16).read s)).1)]
    (if
        (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.1 then ((Operand.ftw : Operand 16).read s) else
        ftwSet ((Operand.ftw : Operand 16).read s) top
        (x87Tag
        (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.2) (6)
        (ccC1C2
        (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.1
        (x87BindVal (FP87.Sin ((Operand.fpr (top) : Operand 80).read s))
        ((Operand.fcw : Operand 16).read s)).2.2.1) s

theorem fsinEffect_components [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState)
    :
    (fsinEffect p len top s).components = [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

attribute [simp] fsinEffect_components

theorem fsin_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ X87BindOk
        (FP87.Sin s.FP87[fprIndex (top)]) s.FP87_Control)
      (codeRange p [0xD9, 0xFE]) (fsinEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fsin_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xFE (by decide)
    (by decide) (by decide) h0 hok hcode.bytesAt hlow
  have hh : (fsinEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 2) _
      (fun t => if
          (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1 then
          t.FP87 else fprSet t.FP87 (fswTop t.FP87_Status)
          (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).1)
      (fun t => if
          (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1 then
          t.FP87_Tag_Word else ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).1))
      (fun t => x87SinFsw t.FP87_Status t.oracle
          (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.1
          (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.1
          (x87BindVal (FP87.Sin t.FP87[fprIndex (fswTop t.FP87_Status)]) t.FP87_Control).2.2.2) _ _
          _ _
      (by
        intro rv hrv
        simp only [List.mem_singleton] at hrv
        subst hrv
        exact fprSet_ite_get_self _ _ _ _)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        exact fprSet_ite_get_of_ne _ _ (Ne.symm hr) _)
      (by
        simp only [Operand.read_ftw, Operand.read_fpr, Operand.read_fcw]
        rfl)
      (by
        simp only [Operand.read_fsw, fswRest_x87SinFsw]
        rfl)
      (by
        exact fswCC_x87SinFsw _ _ _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fsin_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ X87BindOk
        (FP87.Sin s.FP87[fprIndex (top)]) s.FP87_Control)
      (codeRange p [0xD9, 0xFE]) (Effect.post (fsinEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fsinEffect_components]; simp [Component.Covers]) _)
    (fsin_effect_step p top)

attribute [x86_compose] fsinEffect

@[x86_local] theorem fsinEffect_local [Bindings] {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fsinEffect p len top) := by
  effect_local [fsinEffect, x87Effect]

end X86Proofs
