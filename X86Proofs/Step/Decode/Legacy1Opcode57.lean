import X86Proofs.Step.Sse

/-!
# Opcode `0F 57`: `XORPS`, `XORPD`

The one place that looks inside lean-x86's opcode-`57` decoder (`Decode_Legacy_1_Opcode_57`) and its
form selection (`Select_Legacy_1_Opcode_57`), architecture rule 5. In 64-bit mode the selection
picks, without `66` and with SSE, `XORPS_XMMxud_XMMxud` for `mod = 3` and `XORPS_XMMxud_MEMxud`
otherwise (`Instructions/Xorps`, `Instructions/XorpsLoad`, hand-written); after `66` and with SSE2,
`XORPD_XMMxuq_XMMxuq` for `mod = 3` and `XORPD_XMMxuq_MEMxuq` otherwise
(`Instructions/Xorpd/Generated/{XX,XM}`). For each, a `selectLegacy1Opcode57_run_of_…` lemma gives
the form the selection picks, and a `decodeLegacy1Opcode57_run_of_…` lemma runs the decoder (from
the ModRM fetch at `ip + 1`, `ip` the second opcode byte's address) to the call of that form at
`ip + 2`.

The dispatch to this decoder is `decodeLegacy1_run_of_opcode57` (`Step/Escape.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- With `mod = 3`, no `66` prefix, in 64-bit mode with SSE: form 2, `XORPS_XMMxud_XMMxud`. -/
theorem selectLegacy1Opcode57_run_of_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = false)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_57 context true a b true d e f modrm = .ok 2 := by
  simp [Select_Legacy_1_Opcode_57, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- With `mod ≠ 3`, no `66` prefix, in 64-bit mode with SSE: form 1, `XORPS_XMMxud_MEMxud`. -/
theorem selectLegacy1Opcode57_run_of_memory (context : Instruction_Context) (hosz : context.osz_prefix_present = false)
    (a b d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_57 context true a b true d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_57, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/--
The opcode-`0F 57` decoder with a register ModRM (`mod = 3`). If fetching the byte after the
opcode at `ip` returns the ModRM byte and leaves state `t` (in 64-bit mode, decoder features
answered, SSE reported), the decoder runs `XORPS_XMMxud_XMMxud` from `t` with `ip + 2` and the
ModRM fields.
-/
theorem decodeLegacy1Opcode57_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_57 ip context).run s =
      (X86.Instructions.XORPS_XMMxud_XMMxud (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_57
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run_sse t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_57 context mode a b c d e f modrm) _ 2 hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode57_run_of_register context hosz a b d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/--
The opcode-`0F 57` decoder with a memory ModRM (`mod ≠ 3`): as `decodeLegacy1Opcode57_run_of_register`, running
`XORPS_XMMxud_MEMxud`.
-/
theorem decodeLegacy1Opcode57_run_of_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = false) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_57 ip context).run s =
      (X86.Instructions.XORPS_XMMxud_MEMxud (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_57
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run_sse t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_57 context mode a b c d e f modrm) _ 1 hmode hf hsse
    (fun a b d e f => selectLegacy1Opcode57_run_of_memory context hosz a b d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

/-- With `mod ≠ 3` and a `66` prefix in 64-bit mode, with SSE2: form 3, `XORPD_XMMxuq_MEMxuq`. -/
theorem selectLegacy1Opcode57_run_of_66_memory (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 ≠ 3#2) :
    Select_Legacy_1_Opcode_57 context true a b c true e f modrm = .ok 3 := by
  simp [Select_Legacy_1_Opcode_57, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-57 decoder with a `66` prefix and a memory ModRM (`mod ≠ 3`), with SSE2 reported,
runs `XORPD_XMMxuq_MEMxuq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1Opcode57_run_of_66_memory [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 ≠ 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_57 ip context).run s =
      (X86.Instructions.XORPD_XMMxuq_MEMxuq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_57
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode57_run_of_66_memory context hosz a b c e f modrm hmod)

/-- With `mod = 3` and a `66` prefix in 64-bit mode, with SSE2: form 4, `XORPD_XMMxuq_XMMxuq`. -/
theorem selectLegacy1Opcode57_run_of_66_register (context : Instruction_Context)
    (hosz : context.osz_prefix_present = true) (a b c e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_57 context true a b c true e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_57, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, hosz, HAnd.hAnd, AndOp.and, strictAnd]

/-- The opcode-57 decoder with a `66` prefix and a register ModRM (`mod = 3`), with SSE2 reported,
runs `XORPD_XMMxuq_XMMxuq` from the state after the ModRM fetch, at `ip + 2`, with the ModRM fields.
-/
theorem decodeLegacy1Opcode57_run_of_66_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hosz : context.osz_prefix_present = true)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t)
    (hf : DecoderFeatures t)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor t CPUID_SSE2_Encoding true)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_57 ip context).run s =
      (X86.Instructions.XORPD_XMMxuq_XMMxuq (BitVec.add ip 2#64) context (modrm.extractLsb' 6 2)
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_57
  decode_modrm_form_sse2 s t ip hfetch hmode hf hsse2
    (fun a b c e f => selectLegacy1Opcode57_run_of_66_register context hosz a b c e f modrm hmod)

end X86Proofs
