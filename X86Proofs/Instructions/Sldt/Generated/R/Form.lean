
import X86Proofs.Step.Umip
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Sldt.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem sldt_r_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode : In64BitMode s) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0)
    (hlma : s.IA32_EFER.LMA = 1) (hsys : SysRegReadable s)
    (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SLDT_GPRv ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (sldtSpec n s.LDTR.selector) ip) := by
  have hb : (s.VMX_Operation_Mode == VMX_Operation_Type.VMX_Non_Root) = false := by
    simpa using hsys.vmx
  have hu : (s.CR4.extractLsb' 11 1 == 1) = false := by rw [hsys.umip]; rfl
  rcases hn with rfl | rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SLDT_GPRv
    simp only [writeResult, Operand.write_reg64]
    spec_run [Current_Mode => currentMode_run _ hcr0 hlma, MonadState.get => get_run _]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ (cr4UMIP_run s), specM_bind_run _ _ (get_run s)]
    simp only [hu, HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    spec_run [X86.Instructions.Operations.SLDT => sldt_operation _ 64 (by decide),
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SLDT_GPRv
    simp only [writeResult, Operand.write_reg32]
    spec_run [Current_Mode => currentMode_run _ hcr0 hlma, MonadState.get => get_run _]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ (cr4UMIP_run s), specM_bind_run _ _ (get_run s)]
    simp only [hu, HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    spec_run [X86.Instructions.Operations.SLDT => sldt_operation _ 32 (by decide),
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SLDT_GPRv
    simp only [writeResult, Operand.write_reg16]
    spec_run [Current_Mode => currentMode_run _ hcr0 hlma, MonadState.get => get_run _]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ (cr4UMIP_run s), specM_bind_run _ _ (get_run s)]
    simp only [hu, HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    spec_run [X86.Instructions.Operations.SLDT => sldt_operation _ 16 (by decide),
      Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
