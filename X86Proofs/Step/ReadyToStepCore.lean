import X86Proofs.Core.Mode
import Prelude

/-!
# Machine readiness for `step`

`ReadyToStepCore s` lists the machine facts lean-x86's `Step` needs to get from its entry to
`Fetch_And_Execute` without an event, a debug trap or a mode change, and to finish by copying
`Next_IP` into RIP. Every fact is one of `Prelude`'s (`SupportedIntegerCPU`, `ExecutionReady`).
`ReadyToStep` (in `Step/ReadyToStep.lean`) adds the memory facts the fetch needs and the CPUID
facts the decoder needs.

`resetStepFields`, `beforeFetch` and `finishStep` are the per-step bookkeeping `Step` does before
and after `Fetch_And_Execute`.
-/

namespace X86Proofs

open X86 X86.UserProcess

/-- The machine facts `Step` needs before it reaches `Fetch_And_Execute`. -/
structure ReadyToStepCore {σ : Type} (s : X86.State σ) : Prop where
  /-- Flat 64-bit user code segment (`Prelude.SupportedIntegerCPU.cs`). -/
  cs : s.CS = userCodeSegment
  /-- Long mode active. -/
  lma : s.IA32_EFER.LMA = 1
  /-- Virtual-8086 interrupt extensions off, so no VIF/VIP check fires. -/
  cr4 : Prelude.CR4.VirtualInterruptsDisabled s.CR4
  /-- Hardware breakpoints disabled. -/
  debug : Prelude.DR7.BreakpointsDisabled s.DR7
  /-- AET (asynchronous event tracing) disabled. -/
  aet : s.AET_EVENT_CTRL.ENABLE = 0
  event : s.Current_Event = .No_Event
  active : s.Thread_Status = .THREAD_ACTIVE
  sti : s.Event_Blocked.STI_BLOCKING = false
  movss : s.Event_Blocked.MOVSS_BLOCKING = false
  singleStep : s.Debug_Single_Step_Trap_Detected = false
  taskSwitch : s.Debug_Task_Switch_Trap_Detected = false
  breakpoint : s.Debug_Breakpoint_Trap_Detected = false
  busLock : s.Debug_Bus_Lock_Trap_Detected = false
  tf : Prelude.RFLAGS.TrapFlagClear s.RFLAGS
  rf : Prelude.RFLAGS.ResumeFlagClear s.RFLAGS

theorem ReadyToStepCore.of_prelude {processor : X86.Machine.Processor} {s : X86.Machine.RamState}
    (cpu : Prelude.SupportedIntegerCPU processor s)
    (ready : Prelude.ExecutionReady s) : ReadyToStepCore s :=
  ⟨cpu.cs, cpu.efer.lma, cpu.cr4.toVirtualInterruptsDisabled, cpu.debug, cpu.aet, ready.event,
    ready.active, ready.sti, ready.movss, ready.singleStep, ready.taskSwitch, ready.breakpoint,
    ready.busLock, ready.tf, ready.rf⟩

/-- The bookkeeping fields `Step` resets at the start of every step. -/
def resetStepFields {σ : Type} (s : X86.State σ) : X86.State σ :=
  { s with Branch_Taken := false
           Execution_Debug_Cause := .Debug_No_Exception
           «FRED::Event_Delivery_In_Progress» := false
           Concurrent_Exception := { s.Concurrent_Exception with valid := false }
           Default_Error_Code := 0
           Committed_To_Task_Switch := false
           Saving_Task_State_During_Task_Switch := false
           CET_Tracker_Updated := false }

/-- The state `Fetch_And_Execute` starts from: `resetStepFields` plus the cleared RF-pending flag. -/
def beforeFetch {σ : Type} (s : X86.State σ) : X86.State σ :=
  { resetStepFields s with Repeat_String_RF_Pending := false }

/--
What `Step` does after `Fetch_And_Execute` returns `t`: unless the instruction branched, is a
repeating string operation, or is an MSR-list operation in progress, RIP becomes `Next_IP`.
-/
def finishStep {σ : Type} (t : X86.State σ) : X86.State σ :=
  { t with RIP := if !t.Branch_Taken && !t.Repeat_String_Operation && !t.«MSRLIST::In_Process»
      then t.Next_IP else t.RIP }

end X86Proofs
