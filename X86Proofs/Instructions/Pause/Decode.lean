import X86Proofs.Step.FetchImm
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode90
import X86Proofs.Instructions.Pause.Form

/-!
# Decoding `F3 90` (`PAUSE`)

`90` has no ModRM byte; after `F3` its decoder picks `PAUSE`
(`decodeLegacy0Opcode90_run_of_pause`, `Step/Decode/Legacy0Opcode90.lean`).
`decodeLegacy0_run_of_90_pause`: `Decode_Legacy_0` on the opcode at offset `k` of the instruction
(after the prefixes), from the state after `k + 1` fetches.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Decoding `90` at offset `k` with a context after `F3`: `PAUSE` with `Next_IP` past the
opcode. -/
theorem decodeLegacy0_run_of_90_pause [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hrep : ctx.rep_prefix = 243) (bytes : List UInt8) (k : Nat) (hk : k < 15)
    (hb : bytes[k]? = some 0x90) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.PAUSE (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0x90, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcode90 _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0Opcode90_run_of_pause _ _ _ _ hrep (hmode _) hfeatures]

end X86Proofs
