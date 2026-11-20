import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode8B

/-!
# Decoding `8B /r` with a memory operand

`MOV r, r/m` (`8B`) with `mod ≠ 3` selects `MOV_GPRv_MEMv_1`. The decoder fetches the opcode and the
ModRM byte and calls the form at the address after the ModRM byte; the form fetches the SIB and
displacement bytes itself (`Effective_Address`).

- `selectLegacy0Opcode8B_run_of_memory`, `decodeLegacy0Opcode8B_run_of_memory`: the pieces
  (`Step/Decode/Legacy0Opcode8B.lean`; dispatch `decodeLegacy0_run_of_opcode8B`,
  `Step/Decode/Legacy0.lean`).
- `decodeLegacy0_run_of_rex_8B_memory`: `rex 8B modrm rest` (rest: SIB and displacement).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Decoding `rex 8B modrm rest` with `mod ≠ 3` (a memory operand), for any REX byte, stored at RIP
below 4 GiB. From the state after the prefix scan (two fetches), `Decode_Legacy_0` fetches the
opcode and the ModRM byte (two more fetches) and calls `MOV_GPRv_MEMv_1` with RIP + 3 (the address
of `rest`), the REX context and the ModRM fields.
-/
theorem decodeLegacy0_run_of_rex_8B_memory [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (rex :: 0x8B :: modrm :: rest))
    (hlow : s.RIP.toNat + (rex :: 0x8B :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_GPRv_MEMv_1 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x8B :: modrm :: rest) := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x8B, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode8B _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode8B_run_of_memory _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

end X86Proofs
