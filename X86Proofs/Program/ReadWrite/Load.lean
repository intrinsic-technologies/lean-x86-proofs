import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Step.Memory
import X86Proofs.Step.PrefixScan

/-!
# Loads: a memory read into a register

Shared by the forms that read memory into a register without flags (`mov r, m`; later `movzx`):
their form result is `writeResult (dataAccess t "load") (.reg r) v nextIP`, the read's
bookkeeping (oracle bits, a `load` trace event) followed by the register write.

- `MemReadable s addr len`: the precondition of a memory read: the `len` bytes at `addr` lie
  below 4 GiB and are present in RAM. A read may cross a 4 KiB page.
- `LoadPre p addr len`: a load triple's precondition: RIP = `p` and `MemReadable` at `addr s`.
- `SegReg.Ready r base s`: segment register `r` (FS or GS) of `s` can be used for data accesses
  and has base `base`. `SegLoadPre p r base addr len`: a load triple's precondition for an operand
  with a segment override `r`: RIP = `p`, the segment is ready with base `base`, and `MemReadable`
  at `base + addr s`.
- `afterStep_load_rip`, `ReadyToStep.afterStep_load`, `AgreesExcept.afterStep_load`: as for
  `writeResult` (`Program/ReadWrite/WriteResult.lean`): RIP is `nextIP`, the state is ready to step again, and
  only the register and RIP change (memory is untouched).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The `len` bytes at `addr` can be read: below 4 GiB (the identity map) and present in RAM. -/
structure MemReadable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop where
  low : addr.toNat + len ≤ 2^32
  mem : ∀ i, i < len → (s.external[addr + BitVec.ofNat 64 i]?).isSome

/-- Readability depends only on memory. -/
theorem MemReadable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemReadable s addr len) (he : t.external = s.external) : MemReadable t addr len :=
  ⟨h.low, fun i hi => he ▸ h.mem i hi⟩

/-- The precondition of a load triple at `p`: RIP = `p`, and the `len` bytes at the operand's
address (a function of the start state, e.g. `fun s => am.addr s (p + instruction length)`) can be
read. -/
structure LoadPre (p : BitVec 64) (addr : RamState → BitVec 64) (len : Nat) (s : RamState) :
    Prop where
  rip : s.RIP = p
  read : MemReadable s (addr s) len

/-- Segment register `r` (FS or GS) of `s` can be used for data accesses (`SegReady`) and has base
`base`. -/
structure SegReg.Ready (r : SegReg) (base : BitVec 64) (s : RamState) : Prop where
  seg : SegReady (r.read s)
  base : segBase (r.read s) = base

/-- The precondition of a load triple at `p` whose memory operand has a segment override `r` (FS or
GS): RIP = `p`, the segment is ready with base `base`, and the `len` bytes at `base + addr s` (the
operand's offset plus the base, wrapping at 2^64) can be read. -/
structure SegLoadPre (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (addr : RamState → BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  seg : r.Ready base s
  read : MemReadable s (base + addr s) len

@[simp] theorem dataAccess_external (s : RamState) (event : String) :
    (dataAccess s event).external = s.external := rfl

/-- After a load form ending in `writeResult … nextIP`, RIP is `nextIP`. -/
theorem afterStep_load_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (dst : Operand n) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeResult (dataAccess t "load") dst (v t) nextIP).RIP =
      nextIP := by
  cases dst <;>
  simp [afterStep, finishStep, writeResult, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation for a load into a register: only that register, the oracle, the trace,
`Next_IP`, RIP and per-step bookkeeping change. -/
theorem ReadyToStep.afterStep_load [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (dataAccess t "load") (.reg r) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult (dataAccess t "load") (.reg r) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A load into register `r` changes only `r` and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_load (s : RamState) (length : Nat) {n : Nat} (r : BitVec 5)
    (v : RamState → BitVec n) (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .rip] s
      (afterStep s length fun t => writeResult (dataAccess t "load") (.reg r) (v t) nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writeResult (dataAccess t "load") (.reg r) (v t) nextIP)
        (.reg r' : Operand 64)).trans
        (Operand.read_writeResult_of_ne (m := 64) _ hne _ _)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, writeResult, Operand.write, dataAccess,
      afterFetches, beforeFetch, resetStepFields]

end X86Proofs
