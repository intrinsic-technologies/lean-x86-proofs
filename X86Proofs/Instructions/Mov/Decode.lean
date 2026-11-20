import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode89
import X86Proofs.Step.Decode.Legacy0OpcodeC7

/-!
# Decoding MOV's register forms

Symbolic decode lemmas for lean-x86's generated decoder on MOV's register opcodes, with the
ModRM byte, the REX prefix and (for `B8+r`) the register in the opcode left symbolic. Each runs
from the state the step wrapper hands to the decoder (`step_none_legacy0` for no prefix,
`step_rex_legacy0` after a REX prefix) to the call of the form, from the state after the opcode
and ModRM fetches; an immediate is fetched by the form itself.

`89 /r` (`MOV r/m, r`, both operands registers): the same shape as the generated register-register
ALU decode lemmas (`Instructions/Xor/Generated/RR/Decode.lean`, …), written here for opcode `89`.
- `decodeLegacy0_run_of_opcode89` (`Step/Decode/Legacy0.lean`),
  `decodeLegacy0Opcode89_run_of_register` (`Step/Decode/Legacy0Opcode89.lean`, shared with
  `MovStore`): the two halves.
- `decodeLegacy0_run_of_rex_89`: `rex 89 modrm`; `decodeLegacy0_run_of_89`: `89 modrm` with no prefix.

`B8+r` (`MOV r, imm`): one decoder per opcode `B8`–`BF`, all of the same shape and all calling
`MOV_GPRv_IMMv` with the opcode byte, so one lemma covers the eight (`MovImmOpcode`; dispatch
`decodeLegacy0_run_of_opcodeB8toBF`).
- `decodeLegacy0_run_of_movImmOpcode`: `Decode_Legacy_0` on any of `B8`–`BF` calls `MOV_GPRv_IMMv`.
- `decodeLegacy0_run_of_rex_movImm`: `rex op`; `decodeLegacy0_run_of_movImm`: `op` with no prefix.

`C7 /0` (`MOV r/m, imm32`, `mod = 3`):
- `decodeLegacy0_run_of_opcodeC7` (`Step/Decode/Legacy0.lean`),
  `decodeLegacy0OpcodeC7_run_of_register` (`Step/Decode/Legacy0OpcodeC7.lean`, shared with
  `MovStore`): the two halves.
- `decodeLegacy0_run_of_rex_C7`: `rex C7 modrm`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-! ### `89 /r` -/

/--
Decoding `rex 89 modrm` with `mod = 3` (both operands registers), for any REX byte, stored at RIP
below 4 GiB. From the
state after the prefix scan (two fetches), `Decode_Legacy_0` fetches the opcode and the ModRM
byte (two more fetches) and calls `MOV_GPRv_GPRv_89` with `Next_IP` = RIP + 3, the REX context and
the ModRM `reg` and `rm` fields.
-/
theorem decodeLegacy0_run_of_rex_89 [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [rex, 0x89, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_GPRv_GPRv_89 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x89, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x89, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcode89 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode89_run_of_register _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

/--
Decoding `89 modrm` with no prefix and `mod = 3` (both operands registers), stored at RIP below
4 GiB. From the state after the prefix scan (one fetch), `Decode_Legacy_0` fetches the opcode
again and the ModRM byte (two more fetches) and calls `MOV_GPRv_GPRv_89` with `Next_IP` = RIP + 2,
the default 64-bit context (operand size 32) and the ModRM `reg` and `rm` fields.
-/
theorem decodeLegacy0_run_of_89 [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [0x89, modrm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_GPRv_GPRv_89 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x89, modrm] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x89, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode89 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode89_run_of_register _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

/-! ### `B8+r` -/

/-- The register field of a `B8+r` opcode byte (bits 2–0). -/
def opcodeReg (op : UInt8) : BitVec 3 := op.toBitVec.extractLsb' 0 3

/-- `op` is one of the opcodes `B8`–`BF` of `MOV r, imm` (`B8+r`). -/
def MovImmOpcode (op : UInt8) : Prop :=
  op ∈ [0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF]

instance (op : UInt8) : Decidable (MovImmOpcode op) := by unfold MovImmOpcode; infer_instance

theorem MovImmOpcode.legacyOpcode {op : UInt8} (h : MovImmOpcode op) : LegacyOpcode op.toBitVec := by
  simp only [MovImmOpcode, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact legacyOpcode_of_check _ ⟨by decide, by decide⟩

/--
`Decode_Legacy_0` on an opcode byte `B8`–`BF`. Without a REX2 prefix, if fetching the opcode at
`ip` returns `op` and leaves state `u` in 64-bit mode with the decoder's features answered, the
legacy decoder passes its invalid-opcode checks, the opcode's decoder selects its only form, and
it runs `MOV_GPRv_IMMv` from `u` with `Next_IP` `ip + 1` and the opcode byte.
-/
theorem decodeLegacy0_run_of_movImmOpcode [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false) (op : UInt8)
    (hop : MovImmOpcode op) (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u))
    (hmode : In64BitMode u) (hf : DecoderFeatures u) :
    (Decode_Legacy_0 ip context).run s =
      some ((X86.Instructions.MOV_GPRv_IMMv (BitVec.add ip 1#64) context op.toBitVec).run u) := by
  rw [decodeLegacy0_run_of_opcodeB8toBF s u ip context hrex2 op hop hfetch hmode]
  refine congrArg some ?_
  unfold Decode_Legacy_0_Opcode_B8
  refine (decoderSelect_run_noModRM u _ _ 1 hmode hf (by intros; rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := u) rfl).trans ?_
  exact specM_bind_pure_unit_run _ u

/--
Decoding `op imm` (`op` one of `B8`–`BF`) with no prefix, stored at RIP below 4 GiB, followed by
any bytes `rest` (the immediate). From the state after the prefix scan (one fetch),
`Decode_Legacy_0` fetches the opcode again and calls `MOV_GPRv_IMMv` with `Next_IP` = RIP + 1
(the immediate's address), the default 64-bit context and the opcode byte.
-/
theorem decodeLegacy0_run_of_movImm [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : MovImmOpcode op) (rest : List UInt8) (hcode : BytesAt s s.RIP (op :: rest))
    (hlow : s.RIP.toNat + (op :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_GPRv_IMMv (BitVec.add s.RIP 1#64) (legacyContext s.DS)
        op.toBitVec).run (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (op :: rest) := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok op.toBitVec, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode : In64BitMode (afterFetches (beforeFetch s) 2) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  exact decodeLegacy0_run_of_movImmOpcode _ _ _ _ rfl op hop f1 hmode hfeatures

/--
Decoding `rex op imm` (`op` one of `B8`–`BF`), for any REX byte, stored at RIP below 4 GiB,
followed by any bytes `rest` (the immediate). From the state after the prefix scan (two fetches),
`Decode_Legacy_0` fetches the opcode again and calls `MOV_GPRv_IMMv` with `Next_IP` = RIP + 2
(the immediate's address), the REX context and the opcode byte.
-/
theorem decodeLegacy0_run_of_rex_movImm [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hop : MovImmOpcode op) (rest : List UInt8) (hcode : BytesAt s s.RIP (rex :: op :: rest))
    (hlow : s.RIP.toNat + (rex :: op :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_GPRv_IMMv (BitVec.add s.RIP 2#64)
        (rexContext s.DS rex.toBitVec) op.toBitVec).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: op :: rest) := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok op.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_movImmOpcode _ _ _ _ rfl op hop f2 hmode hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

/-! ### `C7 /0` -/

/--
Decoding `rex C7 modrm imm32` with `mod = 3` and `reg = 0`, for any REX byte, stored at RIP below
4 GiB, followed by any bytes `rest` (the immediate). From the state after the prefix scan (two
fetches), `Decode_Legacy_0` fetches the opcode and the ModRM byte (two more fetches) and calls
`MOV_GPRv_IMMz` with `Next_IP` = RIP + 3 (the immediate's address), the REX context and the ModRM
`rm` field.
-/
theorem decodeLegacy0_run_of_rex_C7 [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (rex :: 0xC7 :: modrm :: rest))
    (hlow : s.RIP.toNat + (rex :: 0xC7 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_GPRv_IMMz (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0xC7 :: modrm :: rest) := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xC7, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcodeC7 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeC7_run_of_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

end X86Proofs
