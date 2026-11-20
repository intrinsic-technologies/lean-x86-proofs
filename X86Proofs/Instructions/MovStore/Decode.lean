import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode89
import X86Proofs.Step.Decode.Legacy0OpcodeC6
import X86Proofs.Step.Decode.Legacy0OpcodeC7
import X86Proofs.Step.MemOperand

/-!
# Decoding stores: `89 /r`, `C7 /0`, `C6 /0` with a memory operand

With `mod ≠ 3` (and `reg = 0` for the `C7`/`C6` groups) the decoders select `MOV_MEMv_GPRv_1`,
`MOV_MEMv_IMMz_1` and `MOV_MEMb_IMMb_1`. Each fetches the opcode and the ModRM byte and calls the
form at the address after the ModRM byte; the form fetches the SIB, displacement and immediate
bytes itself.

- Opcodes `89`, `C7` and `C6` are shared with other MOV folders: their
  `decodeLegacy0Opcode89_run_of_memory`, `decodeLegacy0OpcodeC7_run_of_memory`,
  `decodeLegacy0OpcodeC6_run_of_memory` live in `Step/Decode/Legacy0Opcode89.lean`,
  `Step/Decode/Legacy0OpcodeC7.lean` and `Step/Decode/Legacy0OpcodeC6.lean`; the dispatch lemmas
  in `Step/Decode/Legacy0.lean`.
- `decodeLegacy0_run_of_pfx_89_memory`, `decodeLegacy0_run_of_pfx_C7_memory`: `pfx op modrm rest` with one prefix
  byte (a REX byte, or `66`), from the state after the prefix scan (two fetches), for any decode
  context without REX2.
- `decodeLegacy0_run_of_C6_memory`: `C6 modrm rest`, no prefix; `decodeLegacy0_run_of_C6_memory_at`:
  `C6 modrm` at any offset of the instruction (after any prefixes), any context without REX2.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-! ### `89 /r` -/

/-! ### `C7 /0` and `C6 /0` -/

/-! ### From the instruction bytes -/

/-- The fetches of the opcode (offset `i`) and the ModRM byte (offset `i + 1`) of an instruction
at RIP below 4 GiB, after `i + 1` fetches (the prefix scan fetches the opcode once already). -/
theorem memFetch_run_of_bytesAt_opcode_modrm [Bindings] (s : RamState) (h : ReadyToStep s) {bytes : List UInt8}
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (i : Nat)
    (hi : i + 1 < bytes.length) (h15 : i + 1 < 15) :
    (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 i)) 8).run (afterFetches (beforeFetch s) (i + 1)) =
      (.ok bytes[i].toBitVec, afterFetches (beforeFetch s) (i + 2)) ∧
    (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 i)) 1#64) 8).run
        (afterFetches (beforeFetch s) (i + 2)) =
      (.ok bytes[i + 1].toBitVec, afterFetches (beforeFetch s) (i + 3)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  refine ⟨memFetch_run_of_bytesAt (beforeFetch s) (i + 1) h.fetchReady hc hlow i (by omega) (by omega), ?_⟩
  rw [show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 i)) 1#64 =
    BitVec.add s.RIP (BitVec.ofNat 64 (i + 1)) from add_ofNat_add s.RIP i 1]
  exact memFetch_run_of_bytesAt (beforeFetch s) (i + 2) h.fetchReady hc hlow (i + 1) hi (by omega)

/--
Decoding `pfx 89 modrm rest` with `mod ≠ 3`, one prefix byte `pfx` (a REX byte) and the context
`ctx` the prefix scan produced (no REX2). From the state after the prefix scan (two fetches),
`Decode_Legacy_0` fetches the opcode and the ModRM byte and calls `MOV_MEMv_GPRv_1` with RIP + 3.
-/
theorem decodeLegacy0_run_of_pfx_89_memory [Bindings] (s : RamState) (h : ReadyToStep s) (pfx modrm : UInt8)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pfx :: 0x89 :: modrm :: rest))
    (hlow : s.RIP.toNat + (pfx :: 0x89 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) ctx).run (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_MEMv_GPRv_1 (BitVec.add s.RIP 3#64) ctx (modrmMod modrm)
        (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode89 _ _ _ _ hrex2 f2 (hmode 3),
    decodeLegacy0Opcode89_run_of_memory _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

/--
Decoding `pfx C7 modrm rest` with `mod ≠ 3` and `reg = 0`, one prefix byte `pfx` (a REX byte or
`66`) and the context `ctx` the prefix scan produced (no REX2): `Decode_Legacy_0` calls
`MOV_MEMv_IMMz_1` with RIP + 3.
-/
theorem decodeLegacy0_run_of_pfx_C7_memory [Bindings] (s : RamState) (h : ReadyToStep s) (pfx modrm : UInt8)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pfx :: 0xC7 :: modrm :: rest))
    (hlow : s.RIP.toNat + (pfx :: 0xC7 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) ctx).run (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MOV_MEMv_IMMz_1 (BitVec.add s.RIP 3#64) ctx (modrmMod modrm)
        (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  obtain ⟨f2, f3⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeC7 _ _ _ _ hrex2 f2 (hmode 3),
    decodeLegacy0OpcodeC7_run_of_memory _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

/--
Decoding `C6 modrm rest` with no prefix, `mod ≠ 3` and `reg = 0`. From the state after the prefix
scan (one fetch), `Decode_Legacy_0` fetches the opcode again and the ModRM byte and calls
`MOV_MEMb_IMMb_1` with RIP + 2 and the default context.
-/
theorem decodeLegacy0_run_of_C6_memory [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (0xC6 :: modrm :: rest))
    (hlow : s.RIP.toNat + (0xC6 :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.MOV_MEMb_IMMb_1 (BitVec.add s.RIP 2#64) (legacyContext s.DS)
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  obtain ⟨f1, f2⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP (BitVec.ofNat 64 0) = s.RIP from BitVec.add_zero _] at f1 f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeC6 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0OpcodeC6_run_of_memory _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl

/--
Decoding `C6 /0` with `mod ≠ 3` at offset `j` of the instruction (after `j` prefix bytes, as
`step_scan_legacy0` hands over), in any decode context without REX2: `Decode_Legacy_0` fetches
the ModRM byte and calls `MOV_MEMb_IMMb_1` at the address after it.
-/
theorem decodeLegacy0_run_of_C6_memory_at [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xC6) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.MOV_MEMb_IMMb_1 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0xC6 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcodeC6 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0OpcodeC6_run_of_memory a u _ ctx _ hmod hreg hmode hfe hf)

end X86Proofs
