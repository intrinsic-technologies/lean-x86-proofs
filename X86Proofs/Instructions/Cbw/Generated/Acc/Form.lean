import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Cbw.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cdqe_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1) :
    (X86.Instructions.CDQE ip ctx).run s =
      (.ok (), writeResult s (Operand.reg 0 : Operand 64)
        (cbwSpec 64 ((Operand.reg 0 : Operand 32).read s)) ip) := by
  have hcontext :
      {ctx with lock_prefix_present := false, rex_w := 1} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CDQE
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.SIGNEXTEND1 => cbw_operation _ 64 (by decide)]

theorem cwde_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hw : ctx.rex_w = 0) :
    (X86.Instructions.CWDE_2 ip ctx).run s =
      (.ok (), writeResult s (Operand.reg 0 : Operand 32)
        (cbwSpec 32 ((Operand.reg 0 : Operand 16).read s)) ip) := by
  have hcontext :
      {ctx with lock_prefix_present := false, osz_prefix_present := false, rex_w := 0} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CWDE_2
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.SIGNEXTEND1 => cbw_operation _ 32 (by decide)]

theorem cbw_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = true) (hw : ctx.rex_w = 0) :
    (X86.Instructions.CBW_2 ip ctx).run s =
      (.ok (), writeResult s (Operand.reg 0 : Operand 16)
        (cbwSpec 16 ((Operand.reg 0 : Operand 8).read s)) ip) := by
  have hcontext :
      {ctx with lock_prefix_present := false, osz_prefix_present := true, rex_w := 0} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CBW_2
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.SIGNEXTEND1 => cbw_operation _ 16 (by decide)]

end X86Proofs
