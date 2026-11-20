import X86Proofs.Step.Paging
import X86Proofs.Core.Mode

/-!
# Walking lean-x86's generated decoder

Generic pieces for symbolic decode lemmas: lemmas that run lean-x86's generated decoder on a fixed
opcode byte with the operand bits (ModRM, REX) left symbolic. The decoder levels each have one
owner: `Decode_Legacy_0`'s dispatch on the opcode byte is `Step/Decode/Legacy0.lean`'s,
`Decode_Legacy_1`'s (the `0F` map) `Step/Escape.lean`'s; an opcode decoder `Decode_Legacy_0_Opcode_XX`
that several instruction folders use is `Step/Decode/Legacy0OpcodeXX.lean`'s (likewise
`Legacy1Opcode1F`), and one only a single folder uses is that folder's (e.g.
`Instructions/Add/Generated/RR/Decode.lean` for `01`). These are the steps every such lemma takes:

- `decodeLegacy0_modeGuard_run`: `Decode_Legacy_0` checks a list of opcodes that are invalid in
  64-bit mode before it dispatches on the opcode byte; for any other opcode each check passes.
- `decoderSelect_run`: each opcode's decoder reads 64-bit mode and six CPUID features, then a
  generated `Select_…` function picks the form from them and the ModRM byte. If the selection
  does not depend on the features, the features' values do not matter, only that they are read
  without failing (`DecoderFeatures`).
- `decode_modrm_form`: the whole run of a ModRM opcode decoder to one form, given its selection
  (`_lzcnt`, `_cetSS`, `_cmpxchg16b`: a selection that depends on that CPUID feature's answer).

lean-x86's decoder reads the CPUID features through the CPUID binding, not from state fields.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The ModRM `mod` field (bits 7–6): 3 means both operands are registers. -/
def modrmMod (modrm : UInt8) : BitVec 2 := modrm.toBitVec.extractLsb' 6 2

/-- The ModRM `reg` field (bits 5–3): a register operand, or an opcode extension. -/
def modrmReg (modrm : UInt8) : BitVec 3 := modrm.toBitVec.extractLsb' 3 3

/-- The ModRM `rm` field (bits 2–0): a register operand if `mod = 3`, else the address form. -/
def modrmRm (modrm : UInt8) : BitVec 3 := modrm.toBitVec.extractLsb' 0 3

/-- The ModRM byte of two register operands (`mod = 3`): `reg` field `reg`, `rm` field `rm`. -/
def modrmRegs (reg rm : BitVec 3) : UInt8 := UInt8.ofNat (0xC0 + 8 * reg.toNat + rm.toNat)

/-- `modrmRegs` has `mod = 3`. -/
theorem modrmMod_modrmRegs : ∀ reg rm : BitVec 3, modrmMod (modrmRegs reg rm) = 3 := by decide

/-- The `reg` field of `modrmRegs reg rm` is `reg`. -/
theorem modrmReg_modrmRegs : ∀ reg rm : BitVec 3, modrmReg (modrmRegs reg rm) = reg := by decide

/-- The `rm` field of `modrmRegs reg rm` is `rm`. -/
theorem modrmRm_modrmRegs : ∀ reg rm : BitVec 3, modrmRm (modrmRegs reg rm) = rm := by decide

/--
The six CPUID features lean-x86's generated decoders read before choosing a form are answered by
the processor's CPUID binding (with any value). The binding may fail on queries it doesn't
support, which would make the decoder fail.
-/
structure DecoderFeatures [Bindings] (s : RamState) : Prop where
  lzcnt : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding b
  mmx : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding b
  sse : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding b
  sse2 : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding b
  cetSS : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding b
  cmpxchg16b : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding b

theorem DecoderFeatures.of_sameControls [Bindings] {s t : RamState} (hst : SameControls s t)
    (h : DecoderFeatures s) : DecoderFeatures t :=
  ⟨h.lzcnt.imp fun _ => reportsCPUFeature_of_sameControls hst,
    h.mmx.imp fun _ => reportsCPUFeature_of_sameControls hst,
    h.sse.imp fun _ => reportsCPUFeature_of_sameControls hst,
    h.sse2.imp fun _ => reportsCPUFeature_of_sameControls hst,
    h.cetSS.imp fun _ => reportsCPUFeature_of_sameControls hst,
    h.cmpxchg16b.imp fun _ => reportsCPUFeature_of_sameControls hst⟩

/--
The form selection every opcode decoder does. In 64-bit mode, with the decoder's CPUID features
answered, if `select` returns `index` whatever the features are, the decoder continues with
`next index`; the state is unchanged.
-/
theorem decoderSelect_run [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hselect : ∀ a b c d e f, select true a b c d e f = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decoderSelect_run` for a selection that depends on the CPUID LZCNT feature (`F3 0F BD`):
with LZCNT reported as `lz`, if `select` returns `index` for that answer whatever the other
features are, the decoder continues with `next index`. -/
theorem decoderSelect_run_lzcnt [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int) (lz : Bool)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hl : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding lz)
    (hselect : ∀ b c d e f, select true lz b c d e f = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨-, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hl)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decoderSelect_run` for a selection that depends on the CPUID CET_SS feature (`F3 0F 1E FA`,
ENDBR64): with CET_SS reported as `cet`, if `select` returns `index` for that answer whatever the
other features are, the decoder continues with `next index`. -/
theorem decoderSelect_run_cetSS [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int) (cet : Bool)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hc : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding cet)
    (hselect : ∀ a b c d f, select true a b c d cet f = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc'⟩, ⟨d, hd⟩, -, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc')).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decoderSelect_run` for a selection that depends on the CPUID CMPXCHG16B feature
(`REX.W 0F C7 /1`): with CMPXCHG16B reported as `cx`, if `select` returns `index` for that answer
whatever the other features are, the decoder continues with `next index`. -/
theorem decoderSelect_run_cmpxchg16b [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int) (cx : Bool)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hc : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding cx)
    (hselect : ∀ a b c d e, select true a b c d e cx = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc'⟩, ⟨d, hd⟩, ⟨e, he⟩, -⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc')).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/--
One of `Decode_Legacy_0`'s checks for an opcode that is invalid in 64-bit mode, once the opcode
is known not to be that one: in 64-bit mode it passes and decoding continues.
-/
theorem decodeLegacy0_modeGuard_run [Bindings] (s : RamState)
    (next : Unit → X86.Runtime.PartialSpecM X86.Exception RamState Unit) (hmode : In64BitMode s) :
    (do
      let mode ← X86.Runtime.liftTotal In_64Bit_Mode
      if strictAnd mode false then
        let result : Unit ← liftM Report_Invalid_Opcode
        next result
      else
        next ()).run s = (next ()).run s := by
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/--
`decoderSelect_run` for an opcode without a ModRM byte: its decoder hands the selection a zero
byte in place of ModRM.
-/
theorem decoderSelect_run_noModRM [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → BitVec 8 →
      Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.SpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hselect : ∀ a b c d e f, select true a b c d e f 0 = .ok index) :
    (do
      let mode ← In_64Bit_Mode
      let a ← CPUID_LZCNT
      let b ← CPUID_MMX
      let c ← CPUID_SSE
      let d ← CPUID_SSE2
      let e ← CPUID_CET_SS
      let f ← CPUID_CMPXCHG16B
      let z ← Std.Bits.Zero 8
      let i ← liftM (select mode a b c d e f z)
      next i : X86.Runtime.SpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (specM_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine (specM_bind_run _ _ (value := 0) rfl).trans ?_
  refine specM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decoderSelect_run_noModRM` for a decoder that may diverge (`PartialSpecM`: opcodes `AE`,
`AF`, whose `REPE`/`REPNE` forms loop): the reads are lifted with `liftTotal`. -/
theorem decoderSelect_run_noModRM_partial [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → BitVec 8 →
      Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.PartialSpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hselect : ∀ a b c d e f, select true a b c d e f 0 = .ok index) :
    (do
      let mode ← X86.Runtime.liftTotal In_64Bit_Mode
      let a ← X86.Runtime.liftTotal CPUID_LZCNT
      let b ← X86.Runtime.liftTotal CPUID_MMX
      let c ← X86.Runtime.liftTotal CPUID_SSE
      let d ← X86.Runtime.liftTotal CPUID_SSE2
      let e ← X86.Runtime.liftTotal CPUID_CET_SS
      let f ← X86.Runtime.liftTotal CPUID_CMPXCHG16B
      let z ← Std.Bits.Zero 8
      let i ← liftM (select mode a b c d e f z)
      next i : X86.Runtime.PartialSpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (partialSpecM_liftTotal_bind_run _ _ hmode).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine (partialSpecM_bind_run _ _ (value := 0) rfl).trans ?_
  refine partialSpecM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-- `decoderSelect_run` for an opcode decoder that may diverge (`PartialSpecM`: the x87 opcodes
`D8`–`DF`): the reads are lifted with `liftTotal`. -/
theorem decoderSelect_run_partial [Bindings] (s : RamState)
    (select : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Except (X86.Runtime.Error Empty) Int)
    {β : Type} (next : Int → X86.Runtime.PartialSpecM X86.Exception RamState β) (index : Int)
    (hmode : In64BitMode s) (hf : DecoderFeatures s)
    (hselect : ∀ a b c d e f, select true a b c d e f = .ok index) :
    (do
      let mode ← X86.Runtime.liftTotal In_64Bit_Mode
      let a ← X86.Runtime.liftTotal CPUID_LZCNT
      let b ← X86.Runtime.liftTotal CPUID_MMX
      let c ← X86.Runtime.liftTotal CPUID_SSE
      let d ← X86.Runtime.liftTotal CPUID_SSE2
      let e ← X86.Runtime.liftTotal CPUID_CET_SS
      let f ← X86.Runtime.liftTotal CPUID_CMPXCHG16B
      let i ← liftM (select mode a b c d e f)
      next i : X86.Runtime.PartialSpecM X86.Exception RamState β).run s = (next index).run s := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hf
  refine (partialSpecM_liftTotal_bind_run _ _ hmode).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run ha)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hb)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hc)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hd)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run he)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (readCPUIDFeature_run hf)).trans ?_
  refine partialSpecM_bind_run _ _ ?_
  rw [hselect]
  rfl

/-! ### Per-form lemmas of a ModRM opcode decoder

Every one-byte opcode decoder with a ModRM byte has the same shape: fetch the ModRM byte at
`ip + 1`, slice its `mod`, (`reg`,) `rm` fields, select the form (`decoderSelect_run`), and call the
chosen form with `ip + 2` and fields of the ModRM byte. -/

/--
Proof of a per-form lemma for a ModRM opcode decoder, after unfolding the decoder: given the
ModRM fetch `hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)`, 64-bit mode and
the decoder features at `t`, and the selection `hsel : ∀ a b c d e f, Select… context true a b c d
e f modrm = .ok k`, the decoder runs the form `k` from `t`.
-/
macro "decode_modrm_form" s:term:max t:term:max ip:term:max hfetch:term:max hmode:term:max
    hf:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run $t _ _ _ $hmode $hf $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

/-- `decode_modrm_form` for a selection that depends on the CPUID LZCNT feature
(`decoderSelect_run_lzcnt`): `hl` gives its answer `lz`, `hsel : ∀ b c d e f, Select… context true
lz b c d e f modrm = .ok k`. -/
macro "decode_modrm_form_lzcnt" s:term:max t:term:max ip:term:max hfetch:term:max hmode:term:max
    hf:term:max hl:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_lzcnt $t _ _ _ _ $hmode $hf $hl $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

/-- `decode_modrm_form` for a decoder that may diverge (`decoderSelect_run_partial`; the x87
opcodes): the chosen form is a total form run through `liftTotal`, or a `PartialSpecM` form. -/
macro "decode_modrm_form_partial" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hsel:term:max : tactic => `(tactic| (
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ $hfetch).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_partial $t _ _ _ $hmode $hf $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  first
    | exact partialSpecM_liftTotal_bind_pure_unit_run _ $t
    | exact partialSpecM_bind_pure_unit_run _ $t))

/-- `decode_modrm_form` for a selection that depends on the CPUID CET_SS feature
(`decoderSelect_run_cetSS`): `hc` gives its answer `cet`, `hsel : ∀ a b c d f, Select… context
true a b c d cet f modrm = .ok k`. -/
macro "decode_modrm_form_cetSS" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hc:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_cetSS $t _ _ _ _ $hmode $hf $hc $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

/-- `decode_modrm_form` for a selection that depends on the CPUID CMPXCHG16B feature
(`decoderSelect_run_cmpxchg16b`): `hc` gives its answer `cx`, `hsel : ∀ a b c d e, Select… context
true a b c d e cx modrm = .ok k`. -/
macro "decode_modrm_form_cmpxchg16b" s:term:max t:term:max ip:term:max hfetch:term:max
    hmode:term:max hf:term:max hc:term:max hsel:term:max : tactic => `(tactic| (
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 1)) _ (s := $s) rfl).trans ?_
  refine (specM_bind_run _ _ $hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 7 6) _ (s := $t) rfl).trans ?_
  try refine (specM_bind_run (X86.Runtime.sliceInclusive _ 5 3) _ (s := $t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive _ 2 0) _ (s := $t) rfl).trans ?_
  refine (decoderSelect_run_cmpxchg16b $t _ _ _ _ $hmode $hf $hc $hsel).trans ?_
  try simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) $ip 2)) _ (s := $t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ $t))

end X86Proofs
