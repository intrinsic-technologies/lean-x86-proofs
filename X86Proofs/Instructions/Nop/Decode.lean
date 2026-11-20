import X86Proofs.Step.Escape
import X86Proofs.Instructions.Nop.Form
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode90
import X86Proofs.Step.Decode.Legacy1Opcode1F

/-!
# Decoding `90` / `66 90` (`NOP_90`) and `0F 1F /0` with a register operand (`NOP_GPRv_0F1F`)

- `90` has no ModRM byte; its decoder picks `NOP_90` when there is no REP prefix and REX.B is 0
  (with REX.B it is `xchg r8, rax`; with `F3` it is `pause`; the selection and decoder lemmas are
  `Step/Decode/Legacy0Opcode90.lean`'s). `decodeLegacy0_run_of_90` (no prefix) and
  `decodeLegacy0_run_of_66_90` (after `66`) start from the state the step wrappers hand to the decoder.
- `0F 1F` reads a ModRM byte; with `mod = 3` and `reg = 0` its decoder picks `NOP_GPRv_0F1F`
  (`decodeLegacy1Opcode1F_run_of_nop_register`, `Step/Decode/Legacy1Opcode1F.lean`).
  `decodeLegacy1_run_of_0F_1F_register` starts from the state `step_none_legacy1` hands to `Decode_Legacy_1`: the escape
  path end to end.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Decoding `90` (`nop`) at RIP below 4 GiB, from the state after the prefix scan (one fetch):
`NOP_90` with `Next_IP` = RIP + 1. -/
theorem decodeLegacy0_run_of_90 [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x90]) (hlow : s.RIP.toNat + 1 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.NOP_90 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x90] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x90, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode90 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode90_run_of_nop _ _ _ _ rfl rfl (hmode 2) hfeatures]

/-- Decoding `66 90` (`xchg ax, ax`, a two-byte NOP) at RIP below 4 GiB, from the state after the
prefix scan (two fetches): `NOP_90` with `Next_IP` = RIP + 2 in `oszContext`. -/
theorem decodeLegacy0_run_of_66_90 [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x66, 0x90]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (oszContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.NOP_90 (BitVec.add s.RIP 2#64) (oszContext s.DS)).run
        (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x66, 0x90] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x90, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode90 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode90_run_of_nop _ _ _ _ rfl rfl (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

/--
Decoding `0F 1F modrm` with `mod = 3` and `reg = 0` (`nop r32`) at RIP below 4 GiB, from the state
`step_none_legacy1` hands to `Decode_Legacy_1` (two fetches): `Decode_Legacy_1` fetches `1F` again and the
ModRM byte (two more fetches) and calls `NOP_GPRv_0F1F` with `Next_IP` = RIP + 3.
-/
theorem decodeLegacy1_run_of_0F_1F_register [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP [0x0F, 0x1F, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.NOP_GPRv_0F1F (BitVec.add s.RIP 3#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x0F, 0x1F, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x1F, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy1_run_of_opcode1F _ _ _ _ rfl (hmode 3) f2,
    decodeLegacy1Opcode1F_run_of_nop_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]

end X86Proofs
