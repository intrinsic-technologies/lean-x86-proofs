import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode24_run_of_acc (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_24 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_24]
  rfl

theorem decodeLegacy0Opcode24_run_of_acc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_24 ip context).run s =
      (X86.Instructions.AND_AL_IMMb (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_24
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_24 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode24_run_of_acc context)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_24_acc [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (0x24 :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.AND_AL_IMMb (BitVec.add s.RIP 1#64)
        (legacyContext s.DS)).run (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x24 :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0x24 :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x24, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode24 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode24_run_of_acc _ _ _ (hmode 2) hfeatures]

end X86Proofs
