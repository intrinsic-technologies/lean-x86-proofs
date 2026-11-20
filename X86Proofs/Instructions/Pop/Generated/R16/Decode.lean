import X86Proofs.Instructions.Pop.Decode
import X86Proofs.Step.MemOperand

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_pop_at [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (op : UInt8)
    (hop : PopOpcode op) (bytes : List UInt8) (k : Nat) (hk : k < 15)
    (hb : bytes[k]? = some op) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.POP_GPRv_58_0 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx
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
  exact decodeLegacy0_run_of_popOpcode _ _ _ _ hrex2 op hop f1 (hmode _) hfeatures

end X86Proofs
