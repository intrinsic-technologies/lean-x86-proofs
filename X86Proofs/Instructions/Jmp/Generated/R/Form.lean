import X86Proofs.Instructions.Call.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem jmp_r_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true) (hlock : ctx.lock_prefix_present = false)
    (hmode : In64BitMode t) (hready : BranchReady t)
    (htarget : ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read t).toNat <
      2^32) :
    (X86.Instructions.JMP_GPRv ip ctx rm).run t =
      (.ok (), jumpState t ip
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read t)) := by
  have hcontext : ({ ctx with is_mode64 := true, lock_prefix_present := false } :
      Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  simp only [Operand.read_reg64] at htarget ⊢
  unfold X86.Instructions.JMP_GPRv
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.JMP_NEAR => jmp_operation_abs (withNextIP t ip) _ _ _
      (hready.withNextIP ip) htarget]

end X86Proofs
