import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.PrefixScan

/-!
# Step wrappers for a one-byte legacy opcode after a fixed prefix shape

A step wrapper runs `step s` up to lean-x86's legacy decoder (`Decode_Legacy_0`), which stays a
black box: the caller supplies what the decoder does. `step s` scans the prefixes, runs the
decoder at the opcode from the state after the prefix-scan fetches, applies decoded completion,
then copies `Next_IP` into RIP when the completed instruction permits it. Wrapper names are `step_<prefixes>_<map>`, `<map>` being lean-x86's decoder map (`legacy0` =
`Decode_Legacy_0`, one-byte opcodes; `legacy1` = `Decode_Legacy_1`, the `0F` map, in
`Step/PrefixScan.lean`):

- `step_none_legacy0` (no prefix, e.g. `A4`, `movsb`), `step_rex_legacy0` (REX, e.g. `48 31 D8`,
  `xor rax, rbx`), `step_f3_legacy0` (`F3`), `step_f3_rex_legacy0` (`F3` + REX).
- `fetchAndExecute_none`, `fetchAndExecute_rex`, `fetchAndExecute_f3`, `fetchAndExecute_f3_rex`:
  their fetch sides, instances of the general prefix scan (`fetchAndExecute_scan_legacy0`,
  `Step/PrefixScan.lean`) with the context named (`scanContext_rex`, …).

Any other prefix list (`66`, several prefixes) goes through the general scan,
`Step/PrefixScan.lean` (`step_scan_legacy0`, `step_66_legacy0`, `step_66_rex_legacy0`, `step_scan_legacy1`, …).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Fetch side of a REX + legacy-opcode instruction. If `rex :: op :: rest` is stored at RIP and lies
below 4 GiB, then `Fetch_And_Execute` scans the REX prefix and the opcode (two fetches) and hands over to the legacy
decoder at RIP + 1 with the REX bits in the context.
-/
theorem fetchAndExecute_rex [Bindings]
    (s : RamState) (h : ReadyToStep s) (rex op : UInt8) (rest : List UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : LegacyOpcode op.toBitVec)
    (hcode : BytesAt s s.RIP (rex :: op :: rest))
    (hlow : s.RIP.toNat + (rex :: op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded (scanPreservesRepeat op.toBitVec (rexContext s.DS rex.toBitVec)) (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec))).run
        (afterFetches (beforeFetch s) 2) := by
  have := fetchAndExecute_scan_legacy0 s h [rex] op rest (by simpa using hrex.scanPrefix) hop
    (by simp) hcode hlow
  rwa [scanContext_rex _ _ hrex] at this

/--
Step wrapper for a REX + legacy-opcode instruction. Under `ReadyToStep s`, with
`rex :: op :: rest` at RIP and below 4 GiB: if the legacy decoder, run at RIP + 1 from the state after the
prefix scan, returns normally with state `t` in 64-bit mode, then `step s` runs normally and its
result is `finishStep (finishDecoded effectiveRepeat t)`. The decoder premise stays raw;
the result includes the generated REP completion cleanup (`finishDecoded`).
-/
theorem step_rex_legacy0 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (rex op : UInt8) (rest : List UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : LegacyOpcode op.toBitVec)
    (hcode : BytesAt s s.RIP (rex :: op :: rest))
    (hlow : s.RIP.toNat + (rex :: op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded (scanPreservesRepeat op.toBitVec (rexContext s.DS rex.toBitVec)) t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases (scanPreservesRepeat op.toBitVec (rexContext s.DS rex.toBitVec)) <;> rfl) (by cases (scanPreservesRepeat op.toBitVec (rexContext s.DS rex.toBitVec)) <;> rfl))
  rw [fetchAndExecute_rex s h rex op rest hrex hop hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

/-! ### No prefix, `F3`, `F3` + REX -/

/--
Fetch side of a one-byte legacy opcode with no prefix (e.g. `A4`, `movsb`): `Fetch_And_Execute`
fetches the opcode and hands over to the legacy decoder at RIP with the default context.
-/
theorem fetchAndExecute_none [Bindings]
    (s : RamState) (h : ReadyToStep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (op :: rest))
    (hlow : s.RIP.toNat + (op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded (scanPreservesRepeat op.toBitVec (legacyContext s.DS)) (Decode_Legacy_0 s.RIP (legacyContext s.DS))).run (afterFetches (beforeFetch s) 1) := by
  have := fetchAndExecute_scan_legacy0 s h [] op rest (by simp) hop (by simp) hcode hlow
  rwa [scanContext_nil, List.length_nil, show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP
    from BitVec.add_zero _] at this

/-- Step wrapper for a one-byte legacy opcode with no prefix (see `step_rex_legacy0`). -/
theorem step_none_legacy0 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (op :: rest))
    (hlow : s.RIP.toNat + (op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 1) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded (scanPreservesRepeat op.toBitVec (legacyContext s.DS)) t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases (scanPreservesRepeat op.toBitVec (legacyContext s.DS)) <;> rfl) (by cases (scanPreservesRepeat op.toBitVec (legacyContext s.DS)) <;> rfl))
  rw [fetchAndExecute_none s h op rest hop hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

/--
Fetch side of `F3 op` (a REP prefix and a one-byte legacy opcode): two prefix-scan fetches, then
the legacy decoder at RIP + 1 with `rep_prefix = 243`.
-/
theorem fetchAndExecute_f3 [Bindings]
    (s : RamState) (h : ReadyToStep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (0xF3 :: op :: rest))
    (hlow : s.RIP.toNat + (0xF3 :: op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded (scanPreservesRepeat op.toBitVec (repContext s.DS)) (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS))).run
        (afterFetches (beforeFetch s) 2) := by
  exact fetchAndExecute_scan_legacy0 s h [0xF3] op rest (by simp [scanPrefix_f3]) hop (by simp)
    hcode hlow

/-- Step wrapper for `F3 op` (see `step_rex_legacy0`). -/
theorem step_f3_legacy0 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (0xF3 :: op :: rest))
    (hlow : s.RIP.toNat + (0xF3 :: op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded (scanPreservesRepeat op.toBitVec (repContext s.DS)) t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases (scanPreservesRepeat op.toBitVec (repContext s.DS)) <;> rfl) (by cases (scanPreservesRepeat op.toBitVec (repContext s.DS)) <;> rfl))
  rw [fetchAndExecute_f3 s h op rest hop hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

/--
Fetch side of `F3 rex op` (a REP prefix, a REX prefix and a one-byte legacy opcode, e.g.
`F3 48 A5`, `rep movsq`): three prefix-scan fetches, then the legacy decoder at RIP + 2 with
`rep_prefix = 243` and the REX bits. Takes `ReadyMidRep`, so it also covers the iterations of a REP
instruction after the first.
-/
theorem fetchAndExecute_f3_rex [Bindings]
    (s : RamState) (h : ReadyMidRep s) (rex op : UInt8) (rest : List UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : LegacyOpcode op.toBitVec)
    (hcode : BytesAt s s.RIP (0xF3 :: rex :: op :: rest))
    (hlow : s.RIP.toNat + (0xF3 :: rex :: op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded (scanPreservesRepeat op.toBitVec (repRexContext s.DS rex.toBitVec)) (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (repRexContext s.DS rex.toBitVec))).run
        (afterFetches (beforeFetch s) 3) := by
  have := fetchAndExecute_scan_legacy0_of_fetchReady (beforeFetch s) h.fetchReady [0xF3, rex] op
    rest (by simpa [scanPrefix_f3] using hrex.scanPrefix) hop (by simp) hcode hlow
  rwa [scanContext_f3_rex _ _ hrex] at this

/-- Step wrapper for `F3 rex op` (see `step_rex_legacy0`), under `ReadyMidRep` (the
`Repeat_String_Operation` flag may be set). -/
theorem step_f3_rex_legacy0 [Bindings]
    (s t : RamState) (h : ReadyMidRep s) (rex op : UInt8) (rest : List UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : LegacyOpcode op.toBitVec)
    (hcode : BytesAt s s.RIP (0xF3 :: rex :: op :: rest))
    (hlow : s.RIP.toNat + (0xF3 :: rex :: op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (repRexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded (scanPreservesRepeat op.toBitVec (repRexContext s.DS rex.toBitVec)) t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases (scanPreservesRepeat op.toBitVec (repRexContext s.DS rex.toBitVec)) <;> rfl) (by cases (scanPreservesRepeat op.toBitVec (repRexContext s.DS rex.toBitVec)) <;> rfl))
  rw [fetchAndExecute_f3_rex s h rex op rest hrex hop hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

end X86Proofs
