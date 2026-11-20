import X86Proofs.Instructions.Mov.Decode
import X86Proofs.Step.Decode.Legacy0

/-!
# Decoding PUSH r64 (`50+r`)

One decoder per opcode `50`–`57`, all of the same shape: in 64-bit mode each selects its only
64-bit form and calls `PUSH_GPRv_50_0` with the opcode byte, so one lemma covers the eight
(`PushOpcode`), as for `MOV r, imm` (`B8+r`, `decodeLegacy0_run_of_movImmOpcode`). The register is the
opcode's low three bits (`opcodeReg`), extended by REX.B.

- `decodeLegacy0_run_of_pushOpcode`: `Decode_Legacy_0` on any of `50`–`57` calls `PUSH_GPRv_50_0`
  (dispatch `decodeLegacy0_run_of_opcode50to57`, `Step/Decode/Legacy0.lean`).
- `decodeLegacy0_run_of_push`: `op` with no prefix; `decodeLegacy0_run_of_rex_push`: `rex op`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `op` is one of the opcodes `50`–`57` of `PUSH r64` (`50+r`). -/
def PushOpcode (op : UInt8) : Prop :=
  op ∈ [0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57]

instance (op : UInt8) : Decidable (PushOpcode op) := by unfold PushOpcode; infer_instance

theorem PushOpcode.legacyOpcode {op : UInt8} (h : PushOpcode op) : LegacyOpcode op.toBitVec := by
  simp only [PushOpcode, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact legacyOpcode_of_check _ ⟨by decide, by decide⟩

/--
`Decode_Legacy_0` on an opcode byte `50`–`57`. Without a REX2 prefix, if fetching the opcode at
`ip` returns `op` and leaves state `u` in 64-bit mode with the decoder's features answered, the
legacy decoder passes its invalid-opcode checks, the opcode's decoder selects its 64-bit form,
and it runs `PUSH_GPRv_50_0` from `u` with `Next_IP` `ip + 1` and the opcode byte.
-/
theorem decodeLegacy0_run_of_pushOpcode [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false) (op : UInt8)
    (hop : PushOpcode op) (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u))
    (hmode : In64BitMode u) (hf : DecoderFeatures u) :
    (Decode_Legacy_0 ip context).run s =
      some ((X86.Instructions.PUSH_GPRv_50_0 (BitVec.add ip 1#64) context op.toBitVec).run u) := by
  rw [decodeLegacy0_run_of_opcode50to57 s u ip context hrex2 op hop hfetch hmode]
  refine congrArg some ?_
  unfold Decode_Legacy_0_Opcode_50
  refine (decoderSelect_run_noModRM u _ _ 1 hmode hf (by intros; rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := u) rfl).trans ?_
  exact specM_bind_pure_unit_run _ u

/--
Decoding `op` (`op` one of `50`–`57`) with no prefix, stored at RIP below 4 GiB. From the state
after the prefix scan (one fetch), `Decode_Legacy_0` fetches the opcode again and calls
`PUSH_GPRv_50_0` with `Next_IP` = RIP + 1, the default 64-bit context and the opcode byte.
-/
theorem decodeLegacy0_run_of_push [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : PushOpcode op) (hcode : BytesAt s s.RIP [op]) (hlow : s.RIP.toNat + 1 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.PUSH_GPRv_50_0 (BitVec.add s.RIP 1#64) (legacyContext s.DS)
        op.toBitVec).run (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [op] := hcode
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
  exact decodeLegacy0_run_of_pushOpcode _ _ _ _ rfl op hop f1 hmode hfeatures

/--
Decoding `rex op` (`op` one of `50`–`57`), for any REX byte, stored at RIP below 4 GiB. From the
state after the prefix scan (two fetches), `Decode_Legacy_0` fetches the opcode again and calls
`PUSH_GPRv_50_0` with `Next_IP` = RIP + 2, the REX context and the opcode byte.
-/
theorem decodeLegacy0_run_of_rex_push [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hop : PushOpcode op) (hcode : BytesAt s s.RIP [rex, op]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.PUSH_GPRv_50_0 (BitVec.add s.RIP 2#64)
        (rexContext s.DS rex.toBitVec) op.toBitVec).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, op] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok op.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_pushOpcode _ _ _ _ rfl op hop f2 hmode hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

end X86Proofs
