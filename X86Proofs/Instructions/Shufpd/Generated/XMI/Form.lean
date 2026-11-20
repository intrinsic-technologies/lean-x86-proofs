import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form
import X86Proofs.Instructions.Shufp.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SHUFP_lanes

theorem shufpd_xmm_m_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hrep : ctx.rep_prefix = 0)
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
    (halign : lin.toNat % 16 = 0) (hlow : lin.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SHUFPD_XMMpd_MEMpd_IMMb ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let x := (Operand.mem lin : Operand 128).read u
      some (.ok (), writeResult (dataAccess u "load") dst
        (shufpdSpec (dst.read t) x imm) (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run_seg_align u hu seg addr lin hseg 128 (by decide) .Memory_Read
    (.inl rfl) .Explicitly_Aligned (fun _ => halign) hlow hmem
  unfold X86.Instructions.SHUFPD_XMMpd_MEMpd_IMMb
  simp only [haddr, hrep, hlock, hvex, hevex]
  pspec_run [
    Effective_Address => hea,
    Read_XMM => readXMM128_run _ _ hmt,
    Mem_Fetch => hfetch,
    Handle_RIP_Relative_Address => partialSpecM_liftM_run_of_ok hrip _,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    Instructions.Operations.SHUFP_lanes =>
      partialResult_lift_run (shufpd_operation _ _ _) _]
  refine (partialSpecM_liftTotal_run _ (writeXMM128_run _ _ _ ?hm)).trans ?_
  case hm => exact hmode.of_cs_lma_eq rfl rfl
  simp only [writeResult, Operand.write_xmm, Operand.read_xmm, concatBits_xmm_reg]
  rfl

end X86Proofs
