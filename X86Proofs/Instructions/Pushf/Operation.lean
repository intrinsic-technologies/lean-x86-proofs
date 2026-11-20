import X86Proofs.Program.ReadWrite.Rflags

/-!
# PUSHF/PUSHFQ specification

`PUSHFQ` (`9C`) pushes RFLAGS, `PUSHF` (`66 9C`) its low 16 bits (FLAGS). Intel SDM: "the VM and
RF flags (bits 16 and 17) are not copied; instead, the values for these flags are cleared in the
RFLAGS image stored on the stack" (`pushfSpec`). The virtual-8086 path does not apply in 64-bit
mode (`currentMode_run`, `Step/Prefix.lean`).
-/

namespace X86Proofs

/-- The RFLAGS image PUSHF/PUSHFQ pushes, from RFLAGS `r`: `r` with RF (bit 16) and VM (bit 17)
cleared. -/
def pushfSpec (r : BitVec 64) : BitVec 64 := r &&& ~~~0x30000#64

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem setVM_setRF_eq_pushfSpec (r : BitVec 64) :
    RFLAGS_Type.setVM (RFLAGS_Type.setRF r 0) 0 = pushfSpec r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [RFLAGS_Type.setVM, RFLAGS_Type.setRF, pushfSpec, BitVec.getLsbD_and]
  rw [getLsbD_setSlice _ _ _ _ _ hj, getLsbD_setSlice _ _ _ _ _ hj]
  have hb : (~~~0x30000#64).getLsbD j = decide (j ≠ 16 ∧ j ≠ 17) :=
    (show ∀ k : Fin 64, (~~~0x30000#64).getLsbD k.val = decide (k.val ≠ 16 ∧ k.val ≠ 17) by
      decide) ⟨j, hj⟩
  rw [hb]
  by_cases h16 : j = 16
  · subst h16; simp
  · by_cases h17 : j = 17
    · subst h17; simp
    · simp [h16, h17, show ¬ (17 ≤ j ∧ j < 17 + 1) by omega,
        show ¬ (16 ≤ j ∧ j < 16 + 1) by omega]

theorem pushfq_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.Operations.PUSHF 64).run t = (.ok (), pushState t (pushfSpec t.RFLAGS)) := by
  have hv : BitVec.extractLsb' (Int.toNat 0) (Int.toNat 64)
      (RFLAGS_Type.setVM (RFLAGS_Type.setRF t.RFLAGS 0) 0) = pushfSpec t.RFLAGS := by
    rw [← setVM_setRF_eq_pushfSpec]
    exact BitVec.extractLsb'_eq_self
  unfold X86.Instructions.Operations.PUSHF
  spec_run [MonadState.get => get_run _, Current_Mode => currentMode_run _ h.cr0 h.efer.lma,
    RSP => rsp_run _, Push_Stack => pushStack_run t h hss (stackPtr t) _ hw]
  rw [rspWrite_run, hv]
  rfl

theorem pushf_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.Operations.PUSHF 16).run t =
      (.ok (), pushState16 t ((pushfSpec t.RFLAGS).setWidth 16)) := by
  have hv : BitVec.extractLsb' (Int.toNat 0) (Int.toNat 16)
      (RFLAGS_Type.setVM (RFLAGS_Type.setRF t.RFLAGS 0) 0) = (pushfSpec t.RFLAGS).setWidth 16 := by
    rw [← setVM_setRF_eq_pushfSpec]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_setWidth]
  unfold X86.Instructions.Operations.PUSHF
  spec_run [MonadState.get => get_run _, Current_Mode => currentMode_run _ h.cr0 h.efer.lma,
    RSP => rsp_run _, Push_Stack => pushStack16_run t h hss (stackPtr t) _ hw]
  rw [rspWrite_run, hv]
  rfl

end X86Proofs
