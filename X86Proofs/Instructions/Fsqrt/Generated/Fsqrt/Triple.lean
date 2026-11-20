
import X86Proofs.Instructions.Fsqrt.Generated.Fsqrt.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fsqrtEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len
      [(top,
      (x87Sqrt ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)).1)]
    (ftwSet ((Operand.ftw : Operand 16).read s) (top)
        (x87Tag
        (x87Sqrt ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)).1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Sqrt ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)).2.2)
        (2)
        (ccC1
        (x87Sqrt ((Operand.fcw : Operand 16).read s) ((Operand.fpr (top) : Operand 80).read s)).2.1)
        s

@[simp] theorem fsqrtEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) :
    (fsqrtEffect p len top s).components = [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fsqrt_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ X87SqrtOk s.FP87_Control
        s.FP87[fprIndex (top)])
      (codeRange p [0xD9, 0xFA]) (fsqrtEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fsqrt_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xFA (by decide)
    (by decide) (by decide) h0 hok hcode.bytesAt hlow
  have hh : (fsqrtEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status)
          (x87Sqrt t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]).1)
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag (x87Sqrt t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]).1))
      (fun t => x87ArithFsw (t.FP87_Status) t.FP87_Status t.oracle
          (x87Sqrt t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1
          (x87Sqrt t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2) _ _ _ _
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

theorem fsqrt_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ X87SqrtOk s.FP87_Control
        s.FP87[fprIndex (top)])
      (codeRange p [0xD9, 0xFA]) (Effect.post (fsqrtEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fsqrtEffect_components]; simp [Component.Covers]) _)
    (fsqrt_effect_step p top)

attribute [x86_compose] fsqrtEffect

@[x86_local] theorem fsqrtEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fsqrtEffect p len top) := by
  effect_local [fsqrtEffect, x87Effect]

end X86Proofs
