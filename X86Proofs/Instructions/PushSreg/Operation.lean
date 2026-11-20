import X86Proofs.Program.ReadWrite.Stack

/-!
# PUSH of a segment register

`PUSH FS`, `PUSH GS` (`0F A0`, `0F A8`, Intel SDM): push the segment register's selector. At operand
size 64 the selector is zero-extended to 8 bytes; at 16 (`66`) the 2 bytes are pushed.
`pushsregSpec n sel` is the value pushed at operand size `n`. lean-x86's `PUSH_SEG` pushes through
`Push_Stack` (with its LASS check at 64 bits); both sizes are the usual push (`pushState`,
`pushState16`).
-/

namespace X86Proofs

/-- The value `PUSH FS` / `PUSH GS` pushes at operand size `n`: the selector zero-extended. -/
def pushsregSpec (n : Nat) (sel : BitVec 16) : BitVec n := sel.setWidth n

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pushsreg_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (sel : BitVec 16)
    (hw : MemWritable t (pushAddr t) 8) (hmode : In64BitMode t) :
    (X86.Instructions.Operations.PUSH_SEG 64 sel).run t =
      (.ok (), pushState t (pushsregSpec 64 sel)) := by
  have hv : pushsregSpec 64 sel = BitVec.ofNat (Int.toNat 64) sel.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [pushsregSpec]
  rw [hv]
  unfold X86.Instructions.Operations.PUSH_SEG
  spec_run [In_64Bit_Mode => hmode, MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack_run t h hss (stackPtr t) _ hw true, RSP_write => rspWrite_run _ _]

theorem pushsreg16_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (sel : BitVec 16) (hw : MemWritable t (pushAddr16 t) 2)
    (hmode : In64BitMode t) :
    (X86.Instructions.Operations.PUSH_SEG 16 sel).run t =
      (.ok (), pushState16 t (pushsregSpec 16 sel)) := by
  unfold X86.Instructions.Operations.PUSH_SEG
  spec_run [In_64Bit_Mode => hmode, MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack16_run t h hss (stackPtr t) _ hw, RSP_write => rspWrite_run _ _]

end X86Proofs
