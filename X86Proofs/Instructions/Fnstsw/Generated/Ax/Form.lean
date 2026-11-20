import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fnstsw.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fnstsw_ax_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.Instructions.FNSTSW_AX ip ctx).run s =
      (.ok (), (Operand.reg 0 : Operand 16).write
          (x87CtlOut s ip 4 (fswCCOracle s.FP87_Status s.oracle)) s.FP87_Status) := by
  unfold X86.Instructions.FNSTSW_AX
  simp only [hlock]
  spec_run [FP87.Is_Enabled => isEnabled_run hcr0,
    X86.Instructions.Operations.FNSTSW => fnstsw_operation _, AX_write => axWrite_run _ _]

end X86Proofs
