import X86Proofs.Step.Mmx

/-!
# Opcode `0F 77`: `EMMS`

The one place that looks inside lean-x86's opcode-`77` decoder (`Decode_Legacy_1_Opcode_77`) and
its form selection (`Select_Legacy_1_Opcode_77`), architecture rule 5. The opcode has no ModRM byte:
the decoder passes the selection a zero byte. In 64-bit mode, without `66` and with MMX, the
selection picks `EMMS` (`Instructions/Emms/Generated/Emms`), which the decoder runs at `ip + 1`
(`ip` the second opcode byte's address).

The dispatch to this decoder is `decodeLegacy1_run_of_opcode77` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Without `66` in 64-bit mode, with MMX: form 1, `EMMS`. -/
theorem selectLegacy1Opcode77_run_of_mmx (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false) (a c d e f : Bool) (modrm : BitVec 8) :
    Select_Legacy_1_Opcode_77 context true a true c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_77, x86_runtime, pure, Except.pure, hosz, HAnd.hAnd, AndOp.and,
    strictAnd, HOr.hOr, OrOp.or, strictOr]

/-- The opcode-77 decoder without `66`, with MMX reported, runs `EMMS` at `ip + 1` from the same
state. -/
theorem decodeLegacy1Opcode77_run_of_mmx [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true) :
    (Decode_Legacy_1_Opcode_77 ip context).run s =
      (X86.Instructions.EMMS (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_1_Opcode_77
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hmmx)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine (specM_bind_run (X86.Helpers.Std.Bits.Zero 8) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ (s := s)
    (by rw [selectLegacy1Opcode77_run_of_mmx context hosz a c d e f]; rfl)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

end X86Proofs
