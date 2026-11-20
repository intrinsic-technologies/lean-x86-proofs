import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Ldmxcsr.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ldmxcsr_m32_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrep : ctx.rep_prefix = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlow : lin.toNat + 4 ≤ 2^32)
    (hmem : ∀ i, i < 4 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hres : ((Operand.mem lin : Operand 32).read t).extractLsb' 16 16 = 0) :
    (X86.Instructions.LDMXCSR_MEMd ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess t "load") (.mxcsr : Operand 32)
        (ldmxcsrSpec ((Operand.mem lin : Operand 32).read t)) next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 32 (by decide)
    .Memory_Read (.inl rfl) .Normal_Alignment (AlignmentOk.normal _ _) hlow hmem
  unfold X86.Instructions.LDMXCSR_MEMd
  simp only [haddr, hlock, hosz, hrep]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.LDMXCSR => ldmxcsr_operation _ _ hres]

end X86Proofs
