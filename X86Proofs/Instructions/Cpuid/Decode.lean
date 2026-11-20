import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeA2
import X86Proofs.Instructions.Cpuid.Form

/-!
# Decoding `0F A2` (`CPUID`)

`A2` has no ModRM byte; in 64-bit mode its decoder always picks `CPUID`
(`decodeLegacy1OpcodeA2_run_of_cpuid`, `Step/Decode/Legacy1OpcodeA2.lean`).
`decodeLegacy1_run_of_cpuid`: `Decode_Legacy_1` on the second opcode byte at offset `k` of the
instruction, from the state after `k + 1` fetches.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Decoding `A2` after `0F` at offset `k`: `CPUID` with `Next_IP` past the opcode. -/
theorem decodeLegacy1_run_of_cpuid [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (bytes : List UInt8)
    (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xA2) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.CPUID (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xA2, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy1_run_of_opcodeA2 _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1OpcodeA2_run_of_cpuid _ _ _ (hmode _) hfeatures]

end X86Proofs
