import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Push.Decode
import X86Proofs.Instructions.Push.Form

/-!
# Layer 3: PUSH r64 step theorems

- `push_r64_step`: `50+r` with no prefix, registers 0–7 (`push rbp` = `55`, `push rbx` = `53`).
- `push_r64_rex_step`: `REX 50+r`, any of the 16 registers (`push r15` = `41 57`). Any REX byte:
  the operand size is 64 with or without REX.W.

Each result is `afterStep s len fun t => pushState { t with Next_IP := RIP + len } v` with `v` the
register's value in the start state `s`; the precondition beyond the code is that the 8 bytes at
RSP - 8 can be written in place (`MemWritable s (pushAddr s) 8`). Preservation and frame:
`Program/ReadWrite/Stack.lean`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The state a PUSH form starts from: ready for data accesses, flat stack segment, and the bytes
at RSP - 8 still writable (fetches change neither memory nor RSP). -/
private theorem push_start [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) ∧ (afterFetches (beforeFetch s) k).SS = userStackSegment :=
  ⟨h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables, h.cpu.ss⟩

/--
Layer 3 for `push r64` (`50+r` with no prefix), for any of the registers 0–7. If the machine is
ready to step, the opcode byte is at RIP below 4 GiB and the 8 bytes at RSP - 8 can be written in
place, then one `step` runs normally and its result is the layer-2 result (push of register
`op & 7`) with `Next_IP` = RIP + 1, plus the per-step housekeeping.
-/
theorem push_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : PushOpcode op) (hcode : BytesAt s s.RIP [op]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    let src : Operand 64 := .reg (gprNumber 0 0 (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 1 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 1#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_push s h op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 2) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := push_start h 2
  rw [push_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h op [] hop.legacyOpcode hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `push r64` (`REX 50+r`), for any REX byte and any of the 16 registers: as
`push_r64_step`, with the register extended by REX.B and `Next_IP` = RIP + 2.
-/
theorem push_r64_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) (hcode : BytesAt s s.RIP [rex, op])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hw : MemWritable s (pushAddr s) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      pushState { t with Next_IP := BitVec.add s.RIP 2#64 } (src.read s))) := by
  have hdecode := decodeLegacy0_run_of_rex_push s h rex op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := push_start h 3
  rw [push_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op [] hrex hop.legacyOpcode hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
