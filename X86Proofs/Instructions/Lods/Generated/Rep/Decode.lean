import X86Proofs.Step.FetchImm
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0OpcodeAC
import X86Proofs.Step.Decode.Legacy0OpcodeAD

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_AD_rep_lodsq [Bindings] (s : RamState) (h : ReadyMidRep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 243)
    (bytes : List UInt8) (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xAD)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.REP_LODSQ_0 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xAD, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcodeAD _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0OpcodeAD_run_of_rep_lodsq _ _ _ hw hrep (hmode _) hfeatures]

theorem decodeLegacy0_run_of_AD_rep_lodsd [Bindings] (s : RamState) (h : ReadyMidRep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 243)
    (bytes : List UInt8) (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xAD)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.REP_LODSD_2 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xAD, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcodeAD _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0OpcodeAD_run_of_rep_lodsd _ _ _ hosz hw hrep (hmode _) hfeatures]

theorem decodeLegacy0_run_of_AD_rep_lodsw [Bindings] (s : RamState) (h : ReadyMidRep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = true)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 243)
    (bytes : List UInt8) (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xAD)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.REP_LODSW_2 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xAD, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcodeAD _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0OpcodeAD_run_of_rep_lodsw _ _ _ hosz hw hrep (hmode _) hfeatures]

theorem decodeLegacy0_run_of_AC_rep_lodsb [Bindings] (s : RamState) (h : ReadyMidRep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hrep : ctx.rep_prefix = 243)
    (bytes : List UInt8) (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0xAC)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.REP_LODSB_0 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xAC, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcodeAC _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0OpcodeAC_run_of_rep_lodsb _ _ _ hrep (hmode _) hfeatures]

end X86Proofs
