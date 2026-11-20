import X86Proofs.Step.FetchImm
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode98_run_of_cdqe (context : Instruction_Context)
    (hw : context.rex_w = 1) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_98 context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_98, hw, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem decodeLegacy0Opcode98_run_of_cdqe [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hw : context.rex_w = 1)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_98 ip context).run s =
      (X86.Instructions.CDQE (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_98
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_98 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0Opcode98_run_of_cdqe context hw)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_98_cdqe [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hw : ctx.rex_w = 1) (bytes : List UInt8)
    (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0x98) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.CDQE (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0x98, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcode98 _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0Opcode98_run_of_cdqe _ _ _ hw (hmode _) hfeatures]

theorem selectLegacy0Opcode98_run_of_cwde (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_98 context true a b c d e f 0 = .ok 3 := by
  simp [Select_Legacy_0_Opcode_98, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem decodeLegacy0Opcode98_run_of_cwde [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (hw : context.rex_w = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_98 ip context).run s =
      (X86.Instructions.CWDE_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_98
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_98 context mode a b c d e f z) _ 3 hmode hf
    (selectLegacy0Opcode98_run_of_cwde context hosz hw)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_98_cwde [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hw : ctx.rex_w = 0) (bytes : List UInt8)
    (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0x98) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.CWDE_2 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0x98, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcode98 _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0Opcode98_run_of_cwde _ _ _ hosz hw (hmode _) hfeatures]

theorem selectLegacy0Opcode98_run_of_cbw (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hw : context.rex_w = 0) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_98 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_98, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem decodeLegacy0Opcode98_run_of_cbw [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hw : context.rex_w = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_98 ip context).run s =
      (X86.Instructions.CBW_2 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_98
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_98 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode98_run_of_cbw context hosz hw)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_98_cbw [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = true) (hw : ctx.rex_w = 0) (bytes : List UInt8)
    (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0x98) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.CBW_2 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0x98, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcode98 _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0Opcode98_run_of_cbw _ _ _ hosz hw (hmode _) hfeatures]

end X86Proofs
