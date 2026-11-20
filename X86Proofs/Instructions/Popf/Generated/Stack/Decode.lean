import X86Proofs.Step.FetchImm
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy0Opcode9D_run_of_popfq (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_9D context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_9D, hosz, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem decodeLegacy0Opcode9D_run_of_popfq [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_9D ip context).run s =
      (X86.Instructions.POPFQ (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_9D
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_9D context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0Opcode9D_run_of_popfq context hosz)).trans ?_
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_9D_popfq [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (bytes : List UInt8)
    (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0x9D) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.POPFQ (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0x9D, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcode9D _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0Opcode9D_run_of_popfq _ _ _ hosz (hmode _) hfeatures]

theorem selectLegacy0Opcode9D_run_of_popf (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hw : context.rex_w = 0) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_9D context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_0_Opcode_9D, hosz, hw, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem decodeLegacy0Opcode9D_run_of_popf [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (hw : context.rex_w = 0)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_9D ip context).run s =
      (X86.Instructions.POPF (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_9D
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_9D context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy0Opcode9D_run_of_popf context hosz hw)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_9D_popf [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = true) (hw : ctx.rex_w = 0) (bytes : List UInt8)
    (k : Nat) (hk : k < 15) (hb : bytes[k]? = some 0x9D) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.POPF (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx).run
        (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0x9D, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop] at this
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [← add_ofNat_add, decodeLegacy0_run_of_opcode9D _ _ _ _ hrex2 f1 (hmode _),
    decodeLegacy0Opcode9D_run_of_popf _ _ _ hosz hw (hmode _) hfeatures]

end X86Proofs

