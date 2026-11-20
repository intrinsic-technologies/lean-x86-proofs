import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.PrefixScan
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Decode.Legacy0

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode2D_run_of_acc (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_2D context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_2D]
  rfl

theorem decodeLegacy0Opcode2D_run_of_acc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_2D ip context).run s =
      (X86.Instructions.SUB_OrAX_IMMz (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_2D
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_2D context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode2D_run_of_acc context)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_rex_2D_acc [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex : UInt8) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (rex :: 0x2D :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 6 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.SUB_OrAX_IMMz (BitVec.add s.RIP 2#64)
        (rexContext s.DS rex.toBitVec)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x2D :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x2D :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x2D, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode2D _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode2D_run_of_acc _ _ _ (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

theorem decodeLegacy0_run_of_2D_acc [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (0x2D :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.SUB_OrAX_IMMz (BitVec.add s.RIP 1#64)
        (legacyContext s.DS)).run (afterFetches (beforeFetch s) 2)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x2D :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0x2D :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x2D, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode2D _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode2D_run_of_acc _ _ _ (hmode 2) hfeatures]

theorem decodeLegacy0_run_of_66_2D_acc [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (0x66 :: 0x2D :: immBytes 16 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (oszContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.SUB_OrAX_IMMz (BitVec.add s.RIP 2#64)
        (oszContext s.DS)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x66 :: 0x2D :: immBytes 16 imm) := hcode
  have hlow' : s.RIP.toNat + (0x66 :: 0x2D :: immBytes 16 imm).length ≤ 2^32 := by
    simpa using hlow
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x2D, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode2D _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode2D_run_of_acc _ _ _ (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

end X86Proofs
