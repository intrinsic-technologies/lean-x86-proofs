import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Stmxcsr.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem stmxcsr_m32_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrep : ctx.rep_prefix = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hmw : MemWritable t lin 4) :
    (X86.Instructions.STMXCSR_MEMd ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 32) (stmxcsrSpec t.MXCSR)
        next) := by
  have hwrite := logicalMemWrite_run_seg_align _ (ht.withNextIP next) seg addr lin hseg 32
    (by decide) (stmxcsrSpec t.MXCSR) .Normal_Alignment (AlignmentOk.normal _ _) hmw.low
    hmw.mem
  unfold X86.Instructions.STMXCSR_MEMd
  simp only [haddr, hlock, hosz, hrep]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.STMXCSR => stmxcsr_operation _]
  exact hwrite

end X86Proofs
