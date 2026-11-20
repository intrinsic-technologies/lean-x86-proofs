import X86Proofs.Step.FetchImm
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0OpcodeE3_run_of_jrcxz (context : Instruction_Context)
    (haddr : context.address_size = 64)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_E3 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_E3, haddr]
  rfl

theorem decodeLegacy0OpcodeE3_run_of_jrcxz [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (haddr : context.address_size = 64)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_E3 ip context).run s =
      (X86.Instructions.JRCXZ_RELBRb (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_E3
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_E3 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0OpcodeE3_run_of_jrcxz context haddr)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_E3_jrcxz [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (haddr : ctx.address_size = 64)
    (bytes : List UInt8) (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xE3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.JRCXZ_RELBRb (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xE3, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcodeE3 _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0OpcodeE3_run_of_jrcxz _ _ _ haddr (hmode _) hfeatures]

theorem selectLegacy0OpcodeE3_run_of_jecxz (context : Instruction_Context)
    (haddr : context.address_size = 32)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_E3 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_E3, haddr]
  rfl

theorem decodeLegacy0OpcodeE3_run_of_jecxz [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (haddr : context.address_size = 32)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_E3 ip context).run s =
      (X86.Instructions.JECXZ_RELBRb_1 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_E3
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_E3 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeE3_run_of_jecxz context haddr)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_E3_jecxz [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (haddr : ctx.address_size = 32)
    (bytes : List UInt8) (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xE3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.JECXZ_RELBRb_1 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xE3, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcodeE3 _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0OpcodeE3_run_of_jecxz _ _ _ haddr (hmode _) hfeatures]

end X86Proofs
