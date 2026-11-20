import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1Opcode77

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_77_mmx [Bindings] (s : RamState) (h : ReadyToStep s)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (bytes : List UInt8) (j : Nat)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0x77) (hj : j < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.EMMS (BitVec.add s.RIP (BitVec.ofNat 64 (j + 1))) ctx).run
          (afterFetches (beforeFetch s) (j + 2))) := by
  have hst : SameControls s (afterFetches (beforeFetch s) (j + 2)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← add_ofNat_add,
    decodeLegacy1_run_at s h bytes j 0x77 hcode hlow hop hj ctx _
      (fun a u hf hmode => decodeLegacy1_run_of_opcode77 a u _ ctx hrex2 hmode hf),
    decodeLegacy1Opcode77_run_of_mmx (afterFetches (beforeFetch s) (j + 2)) _ ctx hosz
      (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
      (h.features.of_sameControls hst) (reportsCPUFeature_of_sameControls hst hmmx)]

end X86Proofs
