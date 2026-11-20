
import X86Proofs.Instructions.Fcom.Generated.Dcd0.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fcomDcd0Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len []
    (((Operand.ftw : Operand 16).read s))
    (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Compare true ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).2) (15)
        (x87CmpCC
        (x87Compare true ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).1) s

@[simp] theorem fcomDcd0Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (s : RamState) :
    (fcomDcd0Effect p len top i s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fcom_dcd0_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87CompareOk true s.FP87[fprIndex (top)] s.FP87[fprIndex (top + i)])
      (codeRange p [0xDC, modrmRegs 2 i]) (fcomDcd0Effect p 2 top i) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hsrc, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fcom_dcd0_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 2 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0
        (by simpa only [modrmRm_modrmRegs] using hsrc) (by simpa only [modrmRm_modrmRegs] using hok)
        hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fcomDcd0Effect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 0) _
      (fun t => t.FP87)
      (fun t => t.FP87_Tag_Word)
      (fun t => x87CmpFsw t.FP87_Status
          (x87Compare true t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).1
          (x87Compare true t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).2) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_x87CmpFsw]
        rfl)
      (by
        rw [cc_and_15]
        exact fswCC_x87CmpFsw _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fcom_dcd0_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87CompareOk true s.FP87[fprIndex (top)] s.FP87[fprIndex (top + i)])
      (codeRange p [0xDC, modrmRegs 2 i]) (Effect.post (fcomDcd0Effect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fcomDcd0Effect_components]; simp [Component.Covers]) _)
    (fcom_dcd0_effect_step p top i)

attribute [x86_compose] fcomDcd0Effect

@[x86_local] theorem fcomDcd0Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} :
    Effect.Local (fcomDcd0Effect p len top i) := by
  effect_local [fcomDcd0Effect, x87Effect]

end X86Proofs
