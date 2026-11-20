import X86Proofs.Step.Escape
import X86Proofs.Step.Sse
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy1Opcode29

/-!
# Decoding `0F 29 /r` (MOVAPS store)

`MOVAPS xmm/m128, xmm` (`NP 0F 29 /r`). The opcode decoder selects, in 64-bit mode without a `66`
prefix and with SSE reported by CPUID, `MOVAPS_MEMps_XMMps` for `mod ≠ 3` (form 1). After the
prefix scan has consumed the prefixes and `0F 29`, `Decode_Legacy_1` refetches `29`
(`decodeLegacy1_run_of_opcode29`), and the opcode decoder fetches the ModRM byte and calls the form at the
address after it; the form fetches the SIB byte and displacement itself.

- `selectLegacy1Opcode29_run_of_memory`: the form selection, and
  `decodeLegacy1Opcode29_run_of_memory`: the opcode decoder (`Step/Decode/Legacy1Opcode29.lean`,
  which owns opcode `29`'s decoder now that other folders use it).
- `decodeLegacy1_run_of_29_memory`: from the state the scan hands to `Decode_Legacy_1`, for `29` at
  offset `k` of the instruction at RIP (`k = 1` for `0F 29`, `k = 2` for `rex 0F 29`) with a
  memory ModRM.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Decoding `… 0F 29 modrm …` with `mod ≠ 3` (a memory destination), stored at RIP below 4 GiB, with
`29` at offset `k` of the instruction (`k = pre.length + 1` for prefixes `pre`) and the ModRM byte
after it. From the state after the prefix scan (`k + 1` fetches), `Decode_Legacy_1` refetches
`29` and fetches the ModRM byte (two more fetches) and calls `MOVAPS_MEMps_XMMps` with
RIP + `k + 2` (the address after the ModRM byte), the context and the ModRM fields.
-/
theorem decodeLegacy1_run_of_29_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (h29 : bytes[k]? = some 0x29) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOVAPS_MEMps_XMMps (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) = (.ok 0x29, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = 0x29 from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h29)] at this
    exact this
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64) 8).run
      (afterFetches (beforeFetch s) (k + 2)) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) (k + 3)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 2) hf hc hlow (k + 1) hlen hk
    rw [show bytes[k + 1] = modrm from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hm)] at this
    rw [show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 1)) from add_ofNat_add s.RIP k 1]
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hst : SameControls s (afterFetches (beforeFetch s) (k + 3)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [decodeLegacy1_run_of_opcode29 _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1Opcode29_run_of_memory _ _ _ _ hosz _ hmod (hmode _) (h.features.of_sameControls hst)
      (reportsCPUFeature_of_sameControls hst hsse.feature) f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

end X86Proofs
