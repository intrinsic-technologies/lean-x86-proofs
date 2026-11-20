import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Cmpfs.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpss_xmm_m32_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hmt : In64BitMode t) (hmode : In64BitMode u)
    (hsse : Prelude.SupportedSSE Bindings.processor u)
    (hlow : lin.toNat + 4 ≤ 2^32)
    (hmem : ∀ i, i < 4 → (u.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hm : MxcsrPre u)
    (hok : cmpfsOk 32 u.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t)
      ((Operand.mem lin : Operand 32).read u) imm) :
    (X86.Instructions.CMPSS_XMMss_MEMss_IMMb ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.mem lin : Operand 32).read u
      (.ok (), writeResult
        ((Operand.mxcsr : Operand 32).write (dataAccess u "load")
          (mxOr u.MXCSR (cmpfsFlags 32 u.MXCSR (dst.read t) x imm)))
        dst (cmpfsSpec 32 u.MXCSR (dst.read t) x imm) (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run_seg_align u hu seg addr lin hseg 32 (by decide)
    .Memory_Read (.inl rfl) .Normal_Alignment (AlignmentOk.normal _ _) hlow hmem
  unfold X86.Instructions.CMPSS_XMMss_MEMss_IMMb
  simp only [haddr, hlock, hvex, hevex]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with readXMM128_run _ _ hmt
  spec_bind_with hfetch
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.CMP3Sf => cmpfs_operation 32 (by decide) _ _ _ _ (by exact hm) (by exact hok)]
  have hm' : In64BitMode
      { dataAccess u "load" with Next_IP := BitVec.add next 1#64, MXCSR := mxOr u.MXCSR (cmpfsFlags 32
        u.MXCSR ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t)
          ((Operand.mem lin : Operand 32).read u) imm) } :=
    hmode.of_cs_lma_eq rfl rfl
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.write_mxcsr, Operand.read_xmm,
    concatBits_xmm_reg]
  rfl

end X86Proofs
