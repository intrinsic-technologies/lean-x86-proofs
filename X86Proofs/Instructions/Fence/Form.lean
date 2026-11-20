import X86Proofs.Core.Run
import X86Proofs.Core.Operand
import X86.Machine.Step

/-!
# Layer 2: LFENCE, MFENCE, SFENCE

`LFENCE`, `MFENCE` and `SFENCE` (`NP 0F AE /5`, `/6`, `/7` with a register ModRM) check for LOCK,
`66` and REP prefixes, set `Next_IP` and call lean-x86's fence primitive, which this sequential
machine binds to recording a fence event in its trace (`X86.Machine.Bindings.Fence`): no memory
ordering to enforce, nothing an effect sees. The result is `fenceState s ip msg`.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Machine

/-- `s` with `Next_IP := ip` and the fence event `msg` on lean-x86's trace of memory events. -/
def fenceState (s : RamState) (ip : BitVec 64) (msg : String) : RamState :=
  { withNextIP s ip with traceEventsRev := ("isa.memory", msg) :: s.traceEventsRev }

/-- Layer 2 for `LFENCE`: without LOCK, `66` and REP it records a load fence and sets `Next_IP`. -/
theorem lfence_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) :
    (X86.Instructions.LFENCE ip ctx).run s = (.ok (), fenceState s ip "lfence") := by
  simp [X86.Instructions.LFENCE, hlock, hosz, hrep, X86.Instructions.Operations.LFENCE]
  rfl

/-- Layer 2 for `MFENCE`: without LOCK, `66` and REP it records a fence and sets `Next_IP`. -/
theorem mfence_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) :
    (X86.Instructions.MFENCE ip ctx).run s = (.ok (), fenceState s ip "mfence") := by
  simp [X86.Instructions.MFENCE, hlock, hosz, hrep, X86.Instructions.Operations.MFENCE]
  rfl

/-- Layer 2 for `SFENCE`: without LOCK, `66` and REP it records a store fence and sets
`Next_IP`. -/
theorem sfence_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) :
    (X86.Instructions.SFENCE ip ctx).run s = (.ok (), fenceState s ip "sfence") := by
  simp [X86.Instructions.SFENCE, hlock, hosz, hrep, X86.Instructions.Operations.SFENCE]
  rfl

end X86Proofs
