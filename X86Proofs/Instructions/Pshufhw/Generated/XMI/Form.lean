import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Pshufhw.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SHUFH_lanes

theorem pshufhw_xmm_m_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
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
    (hu : DataReady u) (hmode : In64BitMode u)
    (hsse : Prelude.SupportedSSE Bindings.processor u)
    (halign : lin.toNat % 16 = 0) (hlow : lin.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.PSHUFHW_XMMdq_MEMdq_IMMb ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.mem lin : Operand 128).read u
      (.ok (), writeResult (dataAccess u "load") dst
        (pshufhwSpec x imm) (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run_seg_align u hu seg addr lin hseg 128 (by decide) .Memory_Read
    (.inl rfl) .Explicitly_Aligned (fun _ => halign) hlow hmem
  unfold X86.Instructions.PSHUFHW_XMMdq_MEMdq_IMMb
  simp only [haddr, hlock, hvex, hevex]
  refine (specM_bind_run _ _ hea).trans ?_
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
    liftM => liftM_run_of_ok (pshufhw_operation _ _) _]
  have hm' : In64BitMode { dataAccess u "load" with Next_IP := BitVec.add next 1#64 } :=
    hmode.of_cs_lma_eq rfl rfl
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, concatBits_xmm_reg]

end X86Proofs
