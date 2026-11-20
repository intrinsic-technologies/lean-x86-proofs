
import X86Proofs.Step.Umip
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Str.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem str_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hcr0 : Prelude.SupportedIntegerCR0 t.CR0)
    (hlma : t.IA32_EFER.LMA = 1) (hsys : SysRegReadable t)
    (hw : MemWritable t lin 2) :
    (X86.Instructions.STR_MEMw ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 16)
        (strSpec 16 t.TR.selector) next) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 16 (by decide)
    (strSpec 16 t.TR.selector) hw.low hw.mem
  unfold X86.Instructions.STR_MEMw
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  dsimp only
  simp only [hrip]
  spec_run [Check_STR => checkSTR_run _ _ rfl hcr0 hlma hsys,
      X86.Instructions.Operations.STR => str_operation _ 16 (by decide),
      Logical_Mem_Write => hwrite]

end X86Proofs
