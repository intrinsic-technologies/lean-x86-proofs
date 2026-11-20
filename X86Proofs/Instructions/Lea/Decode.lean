import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode.Legacy0

/-!
# Decoding `8D /r` (`lea`)

`LEA r, m` (`8D`) with `mod ≠ 3` selects `LEA_GPRv_AGEN` (form 1; `mod = 3` is invalid in 64-bit
mode). As for `8B`, the decoder fetches the opcode and the ModRM byte and calls the form at the
address after the ModRM byte; the form fetches the SIB and displacement bytes itself
(`Effective_Address`).

- `selectLegacy0Opcode8D_run_of_memory`, `decodeLegacy0Opcode8D_run_of_memory`: the pieces
  (dispatch `decodeLegacy0_run_of_opcode8D`, `Step/Decode/Legacy0.lean`).
- `decodeLegacy0_run_of_rex_8D`: `rex 8D modrm rest` (rest: SIB and displacement).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod ≠ 3` in 64-bit mode, opcode 8D's form selection picks form 1, `LEA_GPRv_AGEN`. -/
theorem selectLegacy0Opcode8D_run_of_memory (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_0_Opcode_8D context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_8D, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-8D decoder with a memory ModRM. If fetching the byte after the opcode at `ip` returns a
ModRM byte with `mod ≠ 3` and leaves state `t` (in 64-bit mode, decoder features answered), the
decoder runs `LEA_GPRv_AGEN` from `t` with `ip + 2` (the address after the ModRM byte) and the
ModRM fields.
-/
theorem decodeLegacy0Opcode8D_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_8D ip context).run s =
      (X86.Instructions.LEA_GPRv_AGEN (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_8D
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_0_Opcode_8D context mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f => selectLegacy0Opcode8D_run_of_memory context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/--
Decoding `rex 8D modrm rest` with `mod ≠ 3`, for any REX byte, stored at RIP
below 4 GiB. From the state after the prefix scan (two fetches), `Decode_Legacy_0` fetches the
opcode and the ModRM byte (two more fetches) and calls `LEA_GPRv_AGEN` with RIP + 3 (the address
of `rest`), the REX context and the ModRM fields.
-/
theorem decodeLegacy0_run_of_rex_8D [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (rex :: 0x8D :: modrm :: rest))
    (hlow : s.RIP.toNat + (rex :: 0x8D :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.LEA_GPRv_AGEN (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x8D :: modrm :: rest) := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x8D, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcode8D _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode8D_run_of_memory _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

end X86Proofs
