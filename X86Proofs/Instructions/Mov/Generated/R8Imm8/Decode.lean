
import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_movImm8_at [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7]) (bytes : List UInt8) (k : Nat)
    (hk : k < 15) (hb : bytes[k]? = some op) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOV_GPR8_IMMb_B0 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 1))) ctx
        op.toBitVec).run (afterFetches (beforeFetch s) (k + 2))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hk0, hop'⟩ := List.getElem?_eq_some_iff.mp hb
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok op.toBitVec, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) h.fetchReady hc hlow k hk0 hk
    rw [hop'] at this
    exact this
  have hmode : In64BitMode (afterFetches (beforeFetch s) (k + 2)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 2)) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [decodeLegacy0_run_of_opcodeB0toB7 _ _ _ _ hrex2 op hop f1 hmode, ← add_ofNat_add]
  refine congrArg some ?_
  unfold Decode_Legacy_0_Opcode_B0
  refine (decoderSelect_run_noModRM _ _ _ 1 hmode hfeatures (by intros; rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) _ 1)) _ (s := _) rfl).trans ?_
  exact specM_bind_pure_unit_run _ _

end X86Proofs
