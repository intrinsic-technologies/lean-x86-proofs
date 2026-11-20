import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WritePair
import X86Proofs.Instructions.Idiv.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem idiv_r_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s) (n : Nat)
    (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false)
    (hdef : IdivDefined ((Operand.reg 2 : Operand n).read s ++ (Operand.reg 0 : Operand n).read s)
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand n).read s)) :
    (X86.Instructions.IDIV_GPRv ip ctx rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let r := idivSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 2 : Operand n).read s ++ (Operand.reg 0 : Operand n).read s)
        (src.read s)
      (.ok (), writePairOutputs s 2 0 r.2.1 r.1 r.2.2 6 ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.IDIV_GPRv
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.IDIV => idiv_operation _ 64 (by decide) _
        (by exact hdef)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.IDIV_GPRv
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      X86.Instructions.Operations.IDIV => idiv_operation _ 32 (by decide) _
        (by exact hdef)]

theorem idiv_r16_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false)
    (hdef : IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s)) :
    (X86.Instructions.IDIV_GPRv ip ctx rm).run s =
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let r := idivSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
        (src.read s)
      (.ok (), writePairOutputs s 2 0 r.2.1 r.1 r.2.2 6 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.IDIV_GPRv
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.IDIV => idiv_operation _ 16 (by decide) _
      (by exact hdef)]

end X86Proofs
