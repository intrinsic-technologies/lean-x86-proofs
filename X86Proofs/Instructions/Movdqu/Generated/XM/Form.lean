import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Movdqu.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movdqu_xmm_m128_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlow : lin.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVDQU_XMMdq_MEMdq ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.mem lin : Operand 128).read t
      (.ok (), writeResult (dataAccess t "load") dst (x)
        next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 128 (by decide)
    .Memory_Read (.inl rfl) .Explicitly_Unaligned (AlignmentOk.unaligned _ _) hlow hmem
  unfold X86.Instructions.MOVDQU_XMMdq_MEMdq
  simp only [haddr, hlock, hvex, hevex]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    liftM => liftM_run_of_ok (movu_operation _) _]
  have hm' : In64BitMode { dataAccess t "load" with Next_IP := next } := hmode.of_cs_lma_eq rfl rfl
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, concatBits_xmm_reg]

end X86Proofs
