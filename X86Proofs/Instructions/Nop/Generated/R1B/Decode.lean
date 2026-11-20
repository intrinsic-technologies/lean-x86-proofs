import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1Opcode1B

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_0F_1B_nop_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0F, 0x1B, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.NOP_GPRv_GPRv_0F1B (BitVec.add s.RIP 3#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x0F, 0x1B, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x1B, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy1_run_of_opcode1B _ _ _ _ rfl (hmode 3) f2,
    decodeLegacy1Opcode1B_run_of_nop_register _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]

end X86Proofs
