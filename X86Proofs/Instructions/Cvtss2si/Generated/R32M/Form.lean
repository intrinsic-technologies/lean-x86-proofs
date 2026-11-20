import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Cvts2si.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cvtss2si_r32_m32_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hevexb : ctx.evex_b = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlow : lin.toNat + 4 ≤ 2^32)
    (hmem : ∀ i, i < 4 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hm : MxcsrPre t)
    (hok : cvts2siOk 32 32 t.MXCSR ((Operand.mem lin : Operand 32).read t)) :
    (X86.Instructions.CVTSS2SI_GPR32d_MEMss ip ctx mod reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.mem lin : Operand 32).read t
      some (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write (dataAccess t "load")
          (mxOr t.MXCSR (cvts2siFlags 32 32 t.MXCSR x)))
        dst (cvts2siSpec 32 32 t.MXCSR x) next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 32 (by decide)
    .Memory_Read (.inl rfl) .Normal_Alignment (AlignmentOk.normal _ _) hlow hmem
  unfold X86.Instructions.CVTSS2SI_GPR32d_MEMss
  simp only [haddr, hlock, hw, writeResult, Operand.write_reg32]
  refine (partialSpecM_liftTotal_bind_run _ _ hea).trans ?_
  refine (partialSpecM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  pspec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.CVTSf2SI => cvts2si_operation 32 32 32 (.inl rfl) (.inl rfl) (.inl rfl) _ _ _ _ hevexb (by exact hm) (by exact hok),
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
