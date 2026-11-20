import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Mov.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movntps_m128_xmm_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (halign : lin.toNat % 16 = 0) (hmw : MemWritable t lin 16) :
    (X86.Instructions.MOVNTPS_MEMdq_XMMps ip ctx mod reg rm).run s =
      let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 128)
        (movSpec (src.read t)) next) := by
  have hwrite := logicalMemWrite_run_seg_align _ (ht.withNextIP next) seg addr lin hseg 128
    (by decide)
    (movSpec ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t))
    .Explicitly_Aligned (fun _ => halign) hmw.low hmw.mem true
  unfold X86.Instructions.MOVNTPS_MEMdq_XMMps
  simp only [haddr, hrep, hlock, hosz]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readXMM128_run _ _ hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    liftM => liftM_run_of_ok (mov_operation_except 128 _) _]
  exact hwrite

end X86Proofs
