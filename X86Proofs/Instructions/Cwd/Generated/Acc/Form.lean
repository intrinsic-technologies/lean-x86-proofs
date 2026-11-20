import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Cwd.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cqo_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1) :
    (X86.Instructions.CQO ip ctx).run s =
      (.ok (), writeResult s (Operand.reg 2 : Operand 64)
        (cwdSpec ((Operand.reg 0 : Operand 64).read s)) ip) := by
  have hcontext :
      {ctx with lock_prefix_present := false, rex_w := 1} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CQO
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.SIGNEXTEND2 => cwd_operation _ 64 (by decide)]

theorem cdq_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hw : ctx.rex_w = 0) :
    (X86.Instructions.CDQ_2 ip ctx).run s =
      (.ok (), writeResult s (Operand.reg 2 : Operand 32)
        (cwdSpec ((Operand.reg 0 : Operand 32).read s)) ip) := by
  have hcontext :
      {ctx with lock_prefix_present := false, osz_prefix_present := false, rex_w := 0} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CDQ_2
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.SIGNEXTEND2 => cwd_operation _ 32 (by decide)]

theorem cwd_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = true) (hw : ctx.rex_w = 0) :
    (X86.Instructions.CWD_2 ip ctx).run s =
      (.ok (), writeResult s (Operand.reg 2 : Operand 16)
        (cwdSpec ((Operand.reg 0 : Operand 16).read s)) ip) := by
  have hcontext :
      {ctx with lock_prefix_present := false, osz_prefix_present := true, rex_w := 0} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CWD_2
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.SIGNEXTEND2 => cwd_operation _ 16 (by decide)]

end X86Proofs
