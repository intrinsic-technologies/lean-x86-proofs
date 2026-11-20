import X86Proofs.Step.Escape
import X86Proofs.Instructions.NopMem.Decode
import X86Proofs.Step.Decode.Legacy1Opcode1C

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_0F_1C_nop_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, NopPrefix p) (hlen : pre.length + 3 ≤ 15) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x1C :: modrm :: rest))
    (hlow : s.RIP.toNat + (pre ++ 0x0F :: 0x1C :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)))
        (scanContext s.DS (PrefixSegments.ofState s) pre)).run (afterFetches (beforeFetch s) (pre.length + 2)) =
      some ((X86.Instructions.NOP_MEMv_GPRv_0F1C (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))
        (scanContext s.DS (PrefixSegments.ofState s) pre) (modrmMod modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (pre.length + 4))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x0F :: 0x1C :: modrm :: rest) := hcode
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 2) hf hc hlow (pre.length + 1)
    (by simp) (by omega)
  have f3 := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3) hf hc hlow (pre.length + 2)
    (by simp) (by omega)
  simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_cons_succ, List.getElem_cons_zero] at f2 f3
  rw [show (beforeFetch s).RIP = s.RIP from rfl] at f2 f3
  rw [show pre.length + 2 + 1 = pre.length + 3 by omega] at f2
  rw [show pre.length + 3 + 1 = pre.length + 4 by omega,
    show pre.length + 2 = pre.length + 1 + 1 by omega, ← add_ofNat_add] at f3
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (pre.length + 4)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcode1C _ _ _ _ (nopContext_scan _ _ pre hpre).rex2 (hmode _) f2,
    decodeLegacy1Opcode1C_run_of_nop_memory _ _ _ _ _ hmod (hmode _) hfeatures f3,
    add_ofNat_add, show pre.length + 1 + 2 = pre.length + 3 by omega]
  rfl

end X86Proofs
