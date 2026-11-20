import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectLegacy1OpcodeA0_run_of_push (context : Instruction_Context) (a b c d e f : Bool) :
    Select_Legacy_1_Opcode_A0 context true a b c d e f 0 = .ok 1 := by
  simp [Select_Legacy_1_Opcode_A0]
  rfl

theorem decodeLegacy1OpcodeA0_run_of_push [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_1_Opcode_A0 ip context).run s =
      (X86.Instructions.PUSH_FS (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_1_Opcode_A0
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_1_Opcode_A0 context mode a b c d e f z) _ 1 hmode hf
    (selectLegacy1OpcodeA0_run_of_push context)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy1_run_of_A0_push [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xA0) (hj : j < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.PUSH_FS (BitVec.add s.RIP (BitVec.ofNat 64 (j + 1))) ctx).run
          (afterFetches (beforeFetch s) (j + 2))) := by
  have hst : SameControls s (afterFetches (beforeFetch s) (j + 2)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← add_ofNat_add,
    decodeLegacy1_run_at s h bytes j 0xA0 hcode hlow hop hj ctx _
      (fun a u hf hmode => decodeLegacy1_run_of_opcodeA0 a u _ ctx hrex2 hmode hf),
    decodeLegacy1OpcodeA0_run_of_push (afterFetches (beforeFetch s) (j + 2)) _ ctx
      (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
      (h.features.of_sameControls hst)]

end X86Proofs
