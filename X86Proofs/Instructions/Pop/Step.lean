import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Pop.Decode
import X86Proofs.Instructions.Pop.Form

/-!
# Layer 3: POP r64 step theorems

- `pop_r64_step`: `58+r` with no prefix, registers 0–7 (`pop rbx` = `5B`, `pop rbp` = `5D`).
- `pop_r64_rex_step`: `REX 58+r`, any of the 16 registers (`pop r15` = `41 5F`). Any REX byte:
  the operand size is 64 with or without REX.W.

Each result is `afterStep s len fun t => popState { t with Next_IP := RIP + len } r`; the
precondition beyond the code is that the 8 bytes at RSP can be read
(`MemReadable s (stackPtr s) 8`; the read may cross a page). Preservation and frame:
`Program/ReadWrite/Stack.lean`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The state a POP form starts from: ready for data accesses, flat stack segment (fetches change
neither memory nor RSP). -/
private theorem pop_start [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) ∧ (afterFetches (beforeFetch s) k).SS = userStackSegment :=
  ⟨h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables, h.cpu.ss⟩

/--
Layer 3 for `pop r64` (`58+r` with no prefix), for any of the registers 0–7. If the machine is
ready to step, the opcode byte is at RIP below 4 GiB and the 8 bytes at RSP can be read, then one
`step` runs normally and its result is the layer-2 result (pop into register `op & 7`) with
`Next_IP` = RIP + 1, plus the per-step housekeeping.
-/
theorem pop_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : PopOpcode op) (hcode : BytesAt s s.RIP [op]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8) :
    X86.Machine.step s = some (.next (afterStep s 1 fun t =>
      popState { t with Next_IP := BitVec.add s.RIP 1#64 } (gprNumber 0 0 (opcodeReg op)))) := by
  have hdecode := decodeLegacy0_run_of_pop s h op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 2) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := pop_start h 2
  rw [pop_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h op [] hop.legacyOpcode hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `pop r64` (`REX 58+r`), for any REX byte and any of the 16 registers: as
`pop_r64_step`, with the register extended by REX.B and `Next_IP` = RIP + 2.
-/
theorem pop_r64_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PopOpcode op) (hcode : BytesAt s s.RIP [rex, op])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hr : MemReadable s (stackPtr s) 8) :
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      popState { t with Next_IP := BitVec.add s.RIP 2#64 }
        (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)))) := by
  have hdecode := decodeLegacy0_run_of_rex_pop s h rex op hop hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := pop_start h 3
  rw [pop_r_form _ _ _ _ rfl rfl rfl hmode hd hss (hr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op [] hrex hop.legacyOpcode hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
