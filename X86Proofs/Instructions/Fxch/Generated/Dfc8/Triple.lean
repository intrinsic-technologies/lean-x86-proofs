
import X86Proofs.Instructions.Fxch.Generated.Dfc8.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fxchDfc8Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len
      [(top + i, ((Operand.fpr (top) : Operand 80).read s)),
      (top, ((Operand.fpr (top + i) : Operand 80).read s))]
    (ftwSet
        (ftwSet ((Operand.ftw : Operand 16).read s) (top + i)
        (x87Tag ((Operand.fpr (top) : Operand 80).read s))) top
        (x87Tag ((Operand.fpr (top + i) : Operand 80).read s)))
    (((Operand.fsw : Operand 16).read s)) (2) (0) s

@[simp] theorem fxchDfc8Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (s : RamState) :
    (fxchDfc8Effect p len top i s).components =
        [.fpr (top + i), .fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fxch_dfc8_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3)
      (codeRange p [0xDF, modrmRegs 1 i]) (fxchDfc8Effect p 2 top i) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hsrc⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fxch_dfc8_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 1 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0
        (by simpa only [modrmRm_modrmRegs] using hsrc) hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fxchDfc8Effect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => fprSet
          (fprSet t.FP87 (fswTop t.FP87_Status + i) t.FP87[fprIndex (fswTop t.FP87_Status)])
          (fswTop t.FP87_Status) t.FP87[fprIndex (fswTop t.FP87_Status + i)])
      (fun t => ftwSet
          (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status + i)
          (x87Tag t.FP87[fprIndex (fswTop t.FP87_Status)])) (fswTop t.FP87_Status)
          (x87Tag t.FP87[fprIndex (fswTop t.FP87_Status + i)]))
      (fun t => fxchStatus t.FP87_Status t.oracle) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrv
        rcases hrv with rfl | rfl
        · x87_simp
          by_cases he : fswTop s.FP87_Status + i = fswTop s.FP87_Status
          · simp only [he, fprSet_get_self]
          · simp only [fprSet_get_of_ne _ (Ne.symm he), fprSet_get_self]
        · x87_simp)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hr
        exact (fprSet_get_of_ne _ (Ne.symm hr.2) _).trans
          (fprSet_get_of_ne _ (Ne.symm hr.1) _))
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fxchStatus]
        rfl)
      (by
        exact fswCC_fxchStatus_c1 _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fxch_dfc8_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3)
      (codeRange p [0xDF, modrmRegs 1 i]) (Effect.post (fxchDfc8Effect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fxchDfc8Effect_components]; simp [Component.Covers]) _)
    (fxch_dfc8_effect_step p top i)

attribute [x86_compose] fxchDfc8Effect

@[x86_local] theorem fxchDfc8Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} :
    Effect.Local (fxchDfc8Effect p len top i) := by
  effect_local [fxchDfc8Effect, x87Effect]

end X86Proofs
