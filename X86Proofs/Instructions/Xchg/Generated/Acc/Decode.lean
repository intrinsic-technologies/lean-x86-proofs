import X86Proofs.Step.FetchImm
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0Opcode90
import X86Proofs.Step.Decode.Legacy0Opcode91

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_xchgAcc [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → ctx.rex_b3 = 1 ∧ ctx.rep_prefix = 0) (bytes : List UInt8) (k : Nat)
    (hk : k < 15) (hb : bytes[k]? = some op) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.XCHG_GPRv_OrAX_0 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx
        op.toBitVec).run (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop'⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok op.toBitVec, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop'] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hb3, hrep⟩ := h90 rfl
    rw [decodeLegacy0_run_of_opcode90 _ _ _ _ hrex2 f1 (hmode _),
      decodeLegacy0Opcode90_run_of_xchg _ _ _ _ hrep hb3 (hmode _) hfeatures]
    rfl
  all_goals
    rw [decodeLegacy0_run_of_opcode91to97 _ _ _ _ hrex2 _ (by decide) f1 (hmode _),
      decodeLegacy0Opcode91_run_of_xchg _ _ _ _ (hmode _) hfeatures]

end X86Proofs
