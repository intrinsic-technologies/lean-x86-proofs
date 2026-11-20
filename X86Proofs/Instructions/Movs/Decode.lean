import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0OpcodeA4
import X86Proofs.Step.Decode.Legacy0OpcodeA5

/-!
# Decoding the string moves `A4` (`movsb`) and `F3 REX.W A5` (`rep movsq`)

Symbolic decode lemmas for lean-x86's generated decoder on the opcode bytes `A4` and `A5`, which
have no ModRM byte; the form depends only on the prefixes in the context:

- `A4` with no REP prefix selects `MOVSB` (form 3); with `F3`, `REP_MOVSB_0` (form 2).
- `A5` with REX.W and `F3` selects `REP_MOVSQ_0` (form 6).

`decodeLegacy0_run_of_A4` and `decodeLegacy0_run_of_F3_rex_A5` take them from the state the step wrappers
(`step_none_legacy0`, `step_f3_rex_legacy0`) hand to the decoder.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Decoding `A4` (`movsb`) stored at RIP below 4 GiB, from the state after the prefix scan (one
fetch): the decoder fetches the opcode again and calls `MOVSB` with `Next_IP` = RIP + 1 and the
default 64-bit context.
-/
theorem decodeLegacy0_run_of_A4 [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xA4]) (hlow : s.RIP.toNat + 1 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOVSB (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xA4] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xA4, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeA4 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0OpcodeA4_run_of_noRep _ _ _ rfl (hmode 2) hfeatures]

/--
Decoding `F3 rex A5` (`rep movsq`, REX.W) stored at RIP below 4 GiB, from the state after the
prefix scan (three fetches): the decoder fetches the opcode again and calls `REP_MOVSQ_0` with
`Next_IP` = RIP + 3 and the REP and REX bits in the context. Under `ReadyMidRep`, so it applies to
every iteration.
-/
theorem decodeLegacy0_run_of_F3_rex_A5 [Bindings] (s : RamState) (h : ReadyMidRep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hcode : BytesAt s s.RIP [0xF3, rex, 0xA5])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (repRexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.REP_MOVSQ_0 (BitVec.add s.RIP 3#64)
        (repRexContext s.DS rex.toBitVec)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF3, rex, 0xA5] := hcode
  have f3 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xA5, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have hw : (repRexContext s.DS rex.toBitVec).rex_w = 1 := by
    simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at hrex
    rcases hrex with h | h | h | h | h | h | h | h <;> simp [repRexContext, rexContext, h]
  rw [decodeLegacy0_run_of_opcodeA5 _ _ _ _ rfl f3 (hmode 4),
    decodeLegacy0OpcodeA5_run_of_rep_rexW _ _ _ rfl hw (hmode 4) hfeatures,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]

end X86Proofs
