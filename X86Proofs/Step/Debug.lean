import X86Proofs.Core.Mode
import Prelude

/-!
# Debug breakpoints

The one file that unfolds lean-x86's breakpoint helpers (`Num_Debug_Breakpoints`,
`Get_Breakpoint_Properties`) and the DR7 fields they read (`DR7.L0`–`L3`, `G0`–`G3`, `RW0`–`RW3`,
`LEN0`–`LEN3`). With `Prelude.DR7.BreakpointsDisabled` (DR7 = `0x400`) no breakpoint is enabled,
so the three checks that loop over them find nothing and leave the state alone: the instruction
breakpoint check of the step wrapper (`getInstructionBreakpointMatch_run`, for `Step/Wrapper.lean`)
and the data breakpoint checks of reads and writes (`checkDataReadBreakpoint_run`,
`checkDataWriteBreakpoint_run`, for `Step/Memory.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.UserProcess

variable {σ : Type}

/-- With breakpoints off, the instruction breakpoint check at RIP (in the flat code segment)
matches nothing. -/
theorem getInstructionBreakpointMatch_run (s : X86.State σ)
    (hcs : s.CS = userCodeSegment) (hlma : s.IA32_EFER.LMA = 1)
    (hdebug : Prelude.DR7.BreakpointsDisabled s.DR7) :
    Get_Instruction_Breakpoint_Match.run s = (.ok (false, 0), s) := by
  unfold Get_Instruction_Breakpoint_Match
  have hg : (get : X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.State σ)).run s = (.ok s, s) :=
    rfl
  rw [specM_bind_run _ _ hg, specM_bind_run _ _ hg, specM_bind_run _ _ hg]
  have hc : (Compute_Linear_Address s.CS s.RIP s.CS).run s = (.ok s.RIP, s) := by
    rw [hcs]
    exact computeLinearAddress_userCodeSegment_run s s.RIP hlma
  rw [specM_bind_run _ _ hc]
  simp [Num_Debug_Breakpoints, x86_runtime, Get_Breakpoint_Properties, X86.DR7.L0, X86.DR7.G0,
    X86.DR7.RW0, X86.DR7.LEN0, X86.DR7.L1, X86.DR7.G1, X86.DR7.RW1, X86.DR7.LEN1, X86.DR7.L2,
    X86.DR7.G2, X86.DR7.RW2, X86.DR7.LEN2, X86.DR7.L3, X86.DR7.G3, X86.DR7.RW3, X86.DR7.LEN3, get,
    getThe, liftM, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont,
    MonadStateOf.get, monadLift, MonadLift.monadLift, pure, ExceptT.pure, StateT.pure, StateT.get,
    ExceptT.lift, Functor.map, StateT.map, Bind.bind, HOr.hOr, OrOp.or, strictOr, HAnd.hAnd,
    AndOp.and, strictAnd, hdebug.value, show List.range 4 = [0,1,2,3] from rfl, List.forIn_cons,
    List.forIn_nil]

/-- With breakpoints off, a data read triggers no breakpoint. -/
theorem checkDataReadBreakpoint_run (s : RamState) (address : BitVec 64) (numBytes : Int)
    (hdebug : Prelude.DR7.BreakpointsDisabled s.DR7) :
    (Check_Data_Read_Breakpoint address numBytes).run s = (.ok (), s) := by
  simp [Check_Data_Read_Breakpoint, Num_Debug_Breakpoints, x86_runtime, Get_Breakpoint_Properties,
    X86.DR7.L0, X86.DR7.G0, X86.DR7.RW0, X86.DR7.LEN0, X86.DR7.L1, X86.DR7.G1, X86.DR7.RW1,
    X86.DR7.LEN1, X86.DR7.L2, X86.DR7.G2, X86.DR7.RW2, X86.DR7.LEN2, X86.DR7.L3, X86.DR7.G3,
    X86.DR7.RW3, X86.DR7.LEN3, get, getThe, liftM, bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
    StateT.bind, ExceptT.bindCont, MonadStateOf.get, monadLift, MonadLift.monadLift, pure,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, Bind.bind,
    HOr.hOr, OrOp.or, strictOr, HAnd.hAnd, AndOp.and, strictAnd, hdebug.value, BP_DataReadOrWrite,
    show List.range 4 = [0,1,2,3] from rfl, List.forIn_cons, List.forIn_nil]

/-- With breakpoints off, a data write triggers no breakpoint. -/
theorem checkDataWriteBreakpoint_run (s : RamState) (address : BitVec 64) (numBytes : Int)
    (hdebug : Prelude.DR7.BreakpointsDisabled s.DR7) :
    (Check_Data_Write_Breakpoint address numBytes).run s = (.ok (), s) := by
  simp [Check_Data_Write_Breakpoint, Num_Debug_Breakpoints, x86_runtime, Get_Breakpoint_Properties,
    X86.DR7.L0, X86.DR7.G0, X86.DR7.RW0, X86.DR7.LEN0, X86.DR7.L1, X86.DR7.G1, X86.DR7.RW1,
    X86.DR7.LEN1, X86.DR7.L2, X86.DR7.G2, X86.DR7.RW2, X86.DR7.LEN2, X86.DR7.L3, X86.DR7.G3,
    X86.DR7.RW3, X86.DR7.LEN3, get, getThe, liftM, bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
    StateT.bind, ExceptT.bindCont, MonadStateOf.get, monadLift, MonadLift.monadLift, pure,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, Bind.bind,
    X86.Runtime.CheckedSlice.read, HOr.hOr, OrOp.or, strictOr, HAnd.hAnd, AndOp.and, strictAnd,
    hdebug.value, BP_DataWrite, show List.range 4 = [0,1,2,3] from rfl, List.forIn_cons,
    List.forIn_nil]

end X86Proofs
