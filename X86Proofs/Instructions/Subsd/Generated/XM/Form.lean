import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Subs.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem subsd_xmm_m64_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (hevexb : ctx.evex_b = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlow : lin.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hm : MxcsrPre t)
    (hok : subsOk 64 t.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t)
      ((Operand.mem lin : Operand 64).read t)) :
    (X86.Instructions.SUBSD_XMMsd_MEMsd ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.mem lin : Operand 64).read t
      (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write (dataAccess t "load")
          (mxOr t.MXCSR (subsFlags 64 t.MXCSR (dst.read t) x)))
        dst (subsSpec 64 t.MXCSR (dst.read t) x) next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 64 (by decide)
    .Memory_Read (.inl rfl) .Normal_Alignment (AlignmentOk.normal _ _) hlow hmem
  unfold X86.Instructions.SUBSD_XMMsd_MEMsd
  simp only [haddr, hlock, hvex, hevex]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readXMM128_run _ _ hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.SUBSf => subs_operation 64 (by decide) _ _ _ _ _ hevexb (by exact hm) (by exact hok)]
  have hm' : In64BitMode
      { dataAccess t "load" with Next_IP := next, MXCSR := mxOr t.MXCSR (subsFlags 64 t.MXCSR
        ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t)
        ((Operand.mem lin : Operand 64).read t)) } :=
    hmode.of_cs_lma_eq rfl rfl
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    concatBits_xmm_reg]
  rfl

end X86Proofs
