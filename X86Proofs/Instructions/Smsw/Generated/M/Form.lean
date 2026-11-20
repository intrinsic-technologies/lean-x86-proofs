
import X86Proofs.Step.Umip
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Smsw.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem smsw_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hsys : SysRegReadable t)
    (hw : MemWritable t lin 2) :
    (X86.Instructions.SMSW_MEMw ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 16)
        (smswSpec 16 t.CR0) next) := by
  have hu : (t.CR4.extractLsb' 11 1 == 1) = false := by rw [hsys.umip]; rfl
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 16 (by decide)
    (smswSpec 16 t.CR0) hw.low hw.mem
  unfold X86.Instructions.SMSW_MEMw
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  dsimp only
  simp only [hrip]
  spec_run [MonadState.get => get_run _]
  simp only [Int.reduceToNat, hu, HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  spec_run [X86.Instructions.Operations.SMSW => smsw_operation _ 16 (by decide) (by exact hsys.vmx),
    Logical_Mem_Write => hwrite]

end X86Proofs
