
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Bsf.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem bsf_r_r_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.BSF_GPRv_GPRv_0 ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand n).read s
      (.ok (), writeOutputs s dst
        (bitScanDest n x (bsfSpec x).1 (dst.read s), (bsfSpec x).2)
        (if x = 0 then n else 0) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.BSF_GPRv_GPRv_0
    simp only [Operand.read_reg64, Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.BSF => bsf_operation _ 64 (by decide) _]
    simp only [gprNumber, Int.reduceAdd, Int.reduceToNat]
    split
    · rename_i h
      simp only [bne_iff_ne, ne_eq] at h
      simp only [h, ↓reduceIte, bitScanDest, mergeGPR_64]
      spec_run [Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
    · rename_i h
      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
      simp only [h, ↓reduceIte, bitScanDest]
      simp only [setFlags, Fin.getElem_fin, Vector.set_getElem_self]
      rfl
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.BSF_GPRv_GPRv_0
    simp only [Operand.read_reg32, Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      X86.Instructions.Operations.BSF => bsf_operation _ 32 (by decide) _]
    simp only [gprNumber, Int.reduceAdd, Int.reduceToNat]
    split
    · rename_i h
      simp only [bne_iff_ne, ne_eq] at h
      simp only [h, ↓reduceIte, bitScanDest, mergeGPR_32]
      spec_run [Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
    · rename_i h
      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
      simp only [h, ↓reduceIte, bitScanDest]
      simp only [setFlags, Fin.getElem_fin, Vector.set_getElem_self]
      rfl

theorem bsf_r16_r16_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.BSF_GPRv_GPRv_0 ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s
      (.ok (), writeOutputs s dst
        (bitScanDest 16 x (bsfSpec x).1 (dst.read s), (bsfSpec x).2)
        (if x = 0 then 16 else 0) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.BSF_GPRv_GPRv_0
  simp only [Operand.read_reg16, Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.BSF => bsf_operation _ 16 (by decide) _]
  simp only [gprNumber, Int.reduceAdd, Int.reduceToNat]
  split
  · rename_i h
    simp only [bne_iff_ne, ne_eq] at h
    simp only [h, ↓reduceIte, bitScanDest]
    spec_run [Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · rename_i h
    simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at h
    simp only [h, ↓reduceIte, bitScanDest]
    simp only [setFlags, Fin.getElem_fin, Vector.set_getElem_self]
    rfl

end X86Proofs
