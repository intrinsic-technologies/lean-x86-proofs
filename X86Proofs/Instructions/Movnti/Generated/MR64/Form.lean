import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Mov.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movnti_m64_r64_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hrep : ctx.rep_prefix = 0)
    (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hmw : MemWritable t lin 8) :
    (X86.Instructions.MOVNTI_MEMq_GPR64 ip ctx mod reg rm).run s =
      let src : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 64)
        (movSpec (src.read t)) next) := by
  have hwrite := logicalMemWrite_run_seg_align _ (ht.withNextIP next) seg addr lin hseg 64
    (by decide)
    (movSpec ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t))
    .Normal_Alignment (AlignmentOk.normal _ _) hmw.low hmw.mem true
  unfold X86.Instructions.MOVNTI_MEMq_GPR64
  simp only [haddr, hrep, hosz, hlock, hw]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readGPR64_run _ _ hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [liftM => liftM_run_of_ok (mov_operation_except 64 _) _]
  exact hwrite

end X86Proofs
