import X86Proofs.Step.PrefixScan
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Address
import X86Proofs.Step.Decode.Legacy0

/-!
# Instructions with a memory operand: decoding and the address after the prefixes

Shared by the step theorems of the memory forms (`Instructions/<Op>/Generated/{RM,MR,…}`,
`Instructions/Call`), which hold for any prefix list `pre` the prefix scan covers and any
addressing shape `am`: the instruction is `pre ++ op :: am.modrm reg :: am.tail` (then any
immediate bytes).

- `AddrContext.rex`, `AddrContext.osz`, `AddrContext.oszRex`, `AddrContext.rep`,
  `AddrContext.repRex`, `AddrContext.repne`, `AddrContext.repneRex`: the decode contexts after a
  REX prefix, `66`, `66` then REX, `F3`, `F3` then REX, `F2`, and `F2` then REX give what the
  address computation reads.
- `decodeLegacy0_run_of_modrm_at`: `Decode_Legacy_0` on the opcode at offset `j` of the instruction
  and the ModRM byte after it, for any opcode decoder (`j` is the number of prefix bytes, as
  `step_scan_legacy0` hands over); `decodeLegacy1_run_of_modrm_at`: the same for `Decode_Legacy_1`
  on the second byte of a `0F` opcode; `decodeLegacy1_run_of_modrm_at_controls`: the same, with
  the opcode decoder also given that the state it starts from has the control registers and
  CPUID configuration of the step's start (an SSE decoder needs the SSE or SSE2 CPUID feature);
  `decodeLegacy1_run_of_modrm_at_controls_partial`: that, for a decoder that may diverge;
  `decodeLegacy1_run_at`: `Decode_Legacy_1` on a `0F` opcode without ModRM (EMMS).
- `getElem?_pre_op`, `getElem?_pre_modrm`, `getElem?_pre_tail`, `getElem?_pre_imm`: the bytes of
  `pre ++ op :: modrm :: rest` by offset (`getElem?_pre_imm`: an immediate after the address bytes);
  `getElem?_pre_esc_op`, `getElem?_pre_esc_modrm`: those of `pre ++ 0x0F :: op :: modrm :: rest`.
- `memAlu_ea`: `Effective_Address` for `am` at offset `pre.length + 2`, run where the decoder leaves
  it; `memAlu_ea_seg`: the same with any segment prefix (`SegAddrContext`; the segment is
  `ctxSegment`); `SegAddrContext.seg_legacy`, `SegAddrContext.seg_rex`: the contexts after an FS or
  GS prefix (and REX); `AddrContext.withSeg`: any context above behind an FS or GS prefix
  (`scanContext_seg_cons`), `segAddr_withSeg` its linear address; `MoffsContext.withSeg`: the same
  for a `moffs` operand (`SegMoffsContext`; `MoffsContext.withAsz` behind `67`,
  `SegMoffsContext32`); `AddrContext.withLock`: any context above behind a
  LOCK prefix (`scanContext_lock_cons`); `AddrContext.withAsz`, `SegAddrContext.withAsz`: behind
  an address-size prefix (`scanContext_asz_cons`), `segAddr_withAsz` its linear address;
  `memAlu_ea32_seg`: `memAlu_ea_seg` at address size 32 (the offset is `AddrMode.offset32`);
  `memAlu_dataReady`: the data-access facts of every state the step passes through before memory
  changes; `memAlu_lockReady` the same for `LockReady` (a
  locked access).
- `add_tail_imm`: the address after the ModRM tail and an immediate byte.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The REX context gives what the address computation reads, if REX.X and REX.B are the
shape's. -/
theorem AddrContext.rex (seg : Segment) (rex : BitVec 8) (am : AddrMode)
    (hx : rexX rex = am.rexX) (hb : rexB rex = am.rexB) : AddrContext (rexContext seg rex) am :=
  ⟨rfl, rfl, rfl, rfl, hb, hx⟩

/-- The decode context after `66` (no REX) gives what the address computation reads, if the shape
needs neither REX.X nor REX.B. -/
theorem AddrContext.osz (seg : Segment) (am : AddrMode) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    AddrContext (oszContext seg) am :=
  ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩

/-- The decode context after `66` and a REX prefix gives what the address computation reads, if
REX.X and REX.B are the shape's. -/
theorem AddrContext.oszRex (seg : Segment) (rex : BitVec 8) (am : AddrMode)
    (hx : rexX rex = am.rexX) (hb : rexB rex = am.rexB) : AddrContext (oszRexContext seg rex) am :=
  ⟨rfl, rfl, rfl, rfl, hb, hx⟩

/-- The decode context after `F3` (no REX) gives what the address computation reads, if the shape
needs neither REX.X nor REX.B. -/
theorem AddrContext.rep (seg : Segment) (am : AddrMode) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    AddrContext (repContext seg) am :=
  ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩

/-- The decode context after `F3` and a REX prefix gives what the address computation reads, if
REX.X and REX.B are the shape's. -/
theorem AddrContext.repRex (seg : Segment) (rex : BitVec 8) (am : AddrMode)
    (hx : rexX rex = am.rexX) (hb : rexB rex = am.rexB) : AddrContext (repRexContext seg rex) am :=
  ⟨rfl, rfl, rfl, rfl, hb, hx⟩

/-- The decode context after `66 F3` (no REX) gives what the address computation reads, if the
shape needs neither REX.X nor REX.B. -/
theorem AddrContext.oszRep (seg : Segment) (segs : PrefixSegments) (am : AddrMode)
    (hx : am.rexX = 0) (hb : am.rexB = 0) : AddrContext (scanContext seg segs [0x66, 0xF3]) am :=
  ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩

/-- The decode context after `F2` (no REX) gives what the address computation reads, if the shape
needs neither REX.X nor REX.B. -/
theorem AddrContext.repne (seg : Segment) (am : AddrMode) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    AddrContext (repneContext seg) am :=
  ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩

/-- The decode context after `F2` and a REX prefix gives what the address computation reads, if
REX.X and REX.B are the shape's. -/
theorem AddrContext.repneRex (seg : Segment) (rex : BitVec 8) (am : AddrMode)
    (hx : rexX rex = am.rexX) (hb : rexB rex = am.rexB) :
    AddrContext (repneRexContext seg rex) am :=
  ⟨rfl, rfl, rfl, rfl, hb, hx⟩

/-- The decode context after a segment prefix for a ready segment `sr` (no REX) gives what the
address computation reads, if the shape needs neither REX.X nor REX.B. -/
theorem SegAddrContext.seg_legacy (seg sr : X86.Helpers.Segment) (hsr : SegReady sr)
    (am : AddrMode) (hx : am.rexX = 0) (hb : am.rexB = 0) : SegAddrContext (segContext seg sr) am :=
  ⟨fun _ => hsr, rfl, rfl, rfl, hb.symm, hx.symm⟩

/-- The decode context after a segment prefix for a ready segment `sr` and a REX prefix gives what
the address computation reads, if REX.X and REX.B are the shape's. -/
theorem SegAddrContext.seg_rex (seg sr : X86.Helpers.Segment) (hsr : SegReady sr) (rex : BitVec 8)
    (am : AddrMode) (hx : rexX rex = am.rexX) (hb : rexB rex = am.rexB) :
    SegAddrContext (segRexContext seg sr rex) am :=
  ⟨fun _ => hsr, rfl, rfl, rfl, hb, hx⟩

@[simp] theorem segAddr_segContext (seg sr : X86.Helpers.Segment) (a : BitVec 64) :
    segAddr (segContext seg sr) a = segBase sr + a := rfl

@[simp] theorem segAddr_segRexContext (seg sr : X86.Helpers.Segment) (rex : BitVec 8)
    (a : BitVec 64) : segAddr (segRexContext seg sr rex) a = segBase sr + a := rfl

/-- A context that gives what the address computation reads, with an FS/GS prefix for a ready
segment `sr` in front (`withSeg`, `scanContext_seg_cons`): any of the prefix shapes above (REX,
`66`, `F3`, …) behind a segment override. -/
theorem AddrContext.withSeg {ctx : Instruction_Context} {am : AddrMode} (h : AddrContext ctx am)
    {sr : X86.Helpers.Segment} (hsr : SegReady sr) : SegAddrContext (withSeg ctx sr) am :=
  ⟨fun _ => hsr, h.mode64, h.b4, h.x4, h.b3, h.x3⟩

/-- A context that gives what the address computation reads still does with a LOCK prefix in front
(`withLock`, `scanContext_lock_cons`). -/
theorem AddrContext.withLock {ctx : Instruction_Context} {am : AddrMode} (h : AddrContext ctx am) :
    AddrContext (withLock ctx) am :=
  ⟨h.seg, h.mode64, h.b4, h.x4, h.b3, h.x3⟩

/-- A context that gives what the address computation reads still does with an address-size
prefix in front (`withAsz`, `scanContext_asz_cons`). -/
theorem AddrContext.withAsz {ctx : Instruction_Context} {am : AddrMode} (h : AddrContext ctx am) :
    AddrContext (withAsz ctx) am :=
  ⟨h.seg, h.mode64, h.b4, h.x4, h.b3, h.x3⟩

/-- `AddrContext.withAsz` for a context that may have a segment override. -/
theorem SegAddrContext.withAsz {ctx : Instruction_Context} {am : AddrMode}
    (h : SegAddrContext ctx am) : SegAddrContext (withAsz ctx) am :=
  ⟨h.seg, h.mode64, h.b4, h.x4, h.b3, h.x3⟩

@[simp] theorem segAddr_withAsz (ctx : Instruction_Context) (a : BitVec 64) :
    segAddr (withAsz ctx) a = segAddr ctx a := rfl

@[simp] theorem segAddr_withSeg (ctx : Instruction_Context) (sr : X86.Helpers.Segment)
    (a : BitVec 64) : segAddr (withSeg ctx sr) a = segBase sr + a := rfl

/-- A context that gives what a `moffs` operand's address reads (`MoffsContext`), with an FS/GS
prefix for a ready segment `sr` in front (`withSeg`). -/
theorem MoffsContext.withSeg {ctx : Instruction_Context} {ds : X86.Helpers.Segment}
    (h : MoffsContext ctx ds) {sr : X86.Helpers.Segment} (hsr : SegReady sr) :
    SegMoffsContext (withSeg ctx sr) ds :=
  ⟨h.addr, fun _ => hsr, h.mode64, fun hs => Bool.noConfusion hs⟩

/-- A context that gives what a `moffs` operand's address reads (`MoffsContext`), behind an
address-size prefix (`withAsz`): its facts at address size 32. -/
theorem MoffsContext.withAsz {ctx : Instruction_Context} {ds : X86.Helpers.Segment}
    (h : MoffsContext ctx ds) : SegMoffsContext32 (withAsz ctx) ds :=
  ⟨rfl, fun hs => absurd (h.seg.symm.trans hs) Bool.false_ne_true, h.mode64, fun _ => h.segment⟩

/--
The opcode at offset `j` of the instruction at RIP (`bytes`, below 4 GiB) and the ModRM byte
after it, for an opcode whose `Decode_Legacy_0` dispatch is `hdisp` and whose decoder, given the
ModRM fetch, is `hdec`: from the state after `j + 1` fetches, `Decode_Legacy_0` at RIP + `j`
fetches both bytes and runs `form` from the state after `j + 3` fetches.
-/
theorem decodeLegacy0_run_of_modrm_at [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (op modrm : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (dec form : X86.Runtime.SpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = some (dec.run u))
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → dec.run a = form.run u) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some (form.run (afterFetches (beforeFetch s) (j + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (j + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) hfeatures]

/--
`decodeLegacy0_run_of_modrm_at` for the `0F` map: the second opcode byte at offset `j` of the
instruction at RIP (`bytes`, below 4 GiB, `j` the number of bytes before it, `0F` included) and
the ModRM byte after it, for an opcode whose `Decode_Legacy_1` dispatch is `hdisp` and whose
decoder, given the ModRM fetch, is `hdec`: from the state after `j + 1` fetches,
`Decode_Legacy_1` at RIP + `j` fetches both bytes and runs `form` from the state after `j + 3`
fetches.
-/
theorem decodeLegacy1_run_of_modrm_at [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (op modrm : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (dec form : X86.Runtime.SpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = some (dec.run u))
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → dec.run a = form.run u) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some (form.run (afterFetches (beforeFetch s) (j + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (j + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) hfeatures]

/--
`Decode_Legacy_1` at the second opcode byte `op` (at offset `j` of `bytes`) of an instruction with
no ModRM byte (`0F 77`, EMMS): the dispatch (`hdisp`) fetches `op` and runs the opcode decoder
`dec` from the state after that fetch, which is the state after `j + 2` fetches.
-/
theorem decodeLegacy1_run_at [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (op : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op) (hj : j < 15)
    (ctx : Instruction_Context) (dec : X86.Runtime.SpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = some (dec.run u)) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some (dec.run (afterFetches (beforeFetch s) (j + 2))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  rw [hop'] at f1
  exact hdisp _ _ f1 (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
`decodeLegacy1_run_of_modrm_at` for an opcode decoder that needs more of the state than
`DecoderFeatures` (an SSE decoder reads the SSE or SSE2 CPUID feature): `hdec` is also given
`SameControls s u`, from which any CPUID feature reported at `s` is reported at `u`
(`reportsCPUFeature_of_sameControls`).
-/
theorem decodeLegacy1_run_of_modrm_at_controls [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (op modrm : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (dec form : X86.Runtime.SpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = some (dec.run u))
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → SameControls s u →
        dec.run a = form.run u) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some (form.run (afterFetches (beforeFetch s) (j + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hst : SameControls s (afterFetches (beforeFetch s) (j + 3)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) (h.features.of_sameControls hst) hst]

/--
`decodeLegacy1_run_of_modrm_at_controls` for an opcode decoder that may diverge (`PartialSpecM`,
e.g. `0F 70`): its dispatch arm and the form it calls are `PartialSpecM` programs (a total form
appears as `liftTotal`).
-/
theorem decodeLegacy1_run_of_modrm_at_controls_partial [Bindings] (s : RamState)
    (h : ReadyToStep s) (bytes : List UInt8) (j : Nat) (op modrm : UInt8)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some op) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (dec form : X86.Runtime.PartialSpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = dec.run u)
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → SameControls s u →
        dec.run a = form.run u) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      form.run (afterFetches (beforeFetch s) (j + 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hst : SameControls s (afterFetches (beforeFetch s) (j + 3)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) (h.features.of_sameControls hst) hst]

/--
`decodeLegacy0_run_of_modrm_at` for an opcode decoder that may diverge (`PartialSpecM`, the x87
opcodes `D8`–`DF`), whose dispatch arm is the decoder itself (`hdisp`, given the opcode byte).
-/
theorem decodeLegacy0_run_of_modrm_at_partial [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (op modrm : UInt8) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some op)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (dec form : X86.Runtime.PartialSpecM X86.Exception RamState Unit)
    (hdisp : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 j)) 8).run a = (.ok op.toBitVec, u) →
      In64BitMode u →
      (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run a = dec.run u)
    (hdec : ∀ a u : RamState,
      (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 j)) 1#64) 8).run a =
        (.ok modrm.toBitVec, u) → In64BitMode u → DecoderFeatures u → dec.run a = form.run u) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      form.run (afterFetches (beforeFetch s) (j + 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  obtain ⟨hj0, hop'⟩ := List.getElem?_eq_some_iff.mp hop
  obtain ⟨hj1, hm'⟩ := List.getElem?_eq_some_iff.mp hm
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) (j + 1) hf hc hlow j hj0 (by omega)
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (j + 2) hf hc hlow (j + 1) hj1 (by omega)
  rw [hop'] at f1
  rw [hm', ← add_ofNat_add] at f2
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (j + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [hdisp _ _ f1 (hmode _), hdec _ _ f2 (hmode _) hfeatures]

/-- The opcode of `pre ++ op :: m :: l` is at offset `pre.length`. -/
theorem getElem?_pre_op (pre : List UInt8) (op m : UInt8) (l : List UInt8) :
    (pre ++ op :: m :: l)[pre.length]? = some op := by simp

/-- The ModRM byte of `pre ++ op :: m :: l` is at offset `pre.length + 1`. -/
theorem getElem?_pre_modrm (pre : List UInt8) (op m : UInt8) (l : List UInt8) :
    (pre ++ op :: m :: l)[pre.length + 1]? = some m := by simp

/-- The second opcode byte of `pre ++ 0x0F :: op :: m :: l` is at offset `pre.length + 1`. -/
theorem getElem?_pre_esc_op (pre : List UInt8) (op m : UInt8) (l : List UInt8) :
    (pre ++ 0x0F :: op :: m :: l)[pre.length + 1]? = some op := by
  rw [List.getElem?_append_right (by omega), show pre.length + 1 - pre.length = 0 + 1 by omega]
  rfl

/-- The ModRM byte of `pre ++ 0x0F :: op :: m :: l` is at offset `pre.length + 2`. -/
theorem getElem?_pre_esc_modrm (pre : List UInt8) (op m : UInt8) (l : List UInt8) :
    (pre ++ 0x0F :: op :: m :: l)[pre.length + 1 + 1]? = some m := by
  rw [List.getElem?_append_right (by omega), show pre.length + 1 + 1 - pre.length = 0 + 1 + 1 by
    omega]
  rfl

/-- The bytes after the ModRM byte of `pre ++ op :: m :: l` start at offset `pre.length + 2`. -/
theorem getElem?_pre_tail (pre : List UInt8) (op m : UInt8) (l : List UInt8) (j : Nat) :
    (pre ++ op :: m :: l)[pre.length + 2 + j]? = l[j]? := by
  rw [List.getElem?_append_right (by omega), show pre.length + 2 + j - pre.length = j + 1 + 1 by
    omega]
  rfl

/-- The immediate after the address bytes of `pre ++ op :: m :: (tail ++ immBytes n v)`: byte `j`
of `v` is at offset `pre.length + 2 + tail.length + j`. -/
theorem getElem?_pre_imm {n : Nat} (pre : List UInt8) (op m : UInt8) (tail : List UInt8)
    (v : BitVec n) : ∀ j < n / 8,
      (pre ++ op :: m :: (tail ++ immBytes n v))[pre.length + 2 + tail.length + j]? =
        some (immByte v j) := by
  intro j hj
  have h := immBytes_getElem?_append (pre ++ op :: m :: tail) v j hj
  rw [show (pre ++ op :: m :: tail).length = pre.length + 2 + tail.length by simp; omega,
    List.append_assoc, List.cons_append, List.cons_append] at h
  exact h

/-- The address computation of `am` at offset `pre.length + 2` of the instruction
`pre ++ op :: am.modrm reg :: (am.tail ++ rest)`, run where the decoder leaves it (after
`pre.length + 3` fetches): it fetches `am.tail` and returns `am`'s offset, segment, the address
after the tail and whether the operand is RIP-relative. -/
theorem memAlu_ea [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8) (op : UInt8)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (rest : List UInt8)
    (ctx : Instruction_Context) (hctx : AddrContext ctx am)
    (hcode : BytesAt s s.RIP (pre ++ op :: am.modrm reg :: (am.tail ++ rest)))
    (hlow : s.RIP.toNat + (pre ++ op :: am.modrm reg :: (am.tail ++ rest)).length ≤ 2^32)
    (h15 : pre.length + 2 + am.tail.length ≤ 15) :
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))).run
        (afterFetches (beforeFetch s) (pre.length + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: am.modrm reg :: (am.tail ++ rest)) := hcode
  refine effectiveAddress_run (beforeFetch s) (pre.length + 3) h.fetchReady h.cpu.ds h.cpu.ss am
    hv ctx hctx hc hlow (pre.length + 2) (fun j hj => ?_) (by simp; omega) h15
  rw [getElem?_pre_tail, List.getElem?_append_left hj]

/-- `memAlu_ea` with any segment prefix (`SegAddrContext`): the segment returned is
`ctxSegment ctx am.isStack` (FS or GS after a segment prefix, else the flat segment). -/
theorem memAlu_ea_seg [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8) (op : UInt8)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (rest : List UInt8)
    (ctx : Instruction_Context) (hctx : SegAddrContext ctx am)
    (hcode : BytesAt s s.RIP (pre ++ op :: am.modrm reg :: (am.tail ++ rest)))
    (hlow : s.RIP.toNat + (pre ++ op :: am.modrm reg :: (am.tail ++ rest)).length ≤ 2^32)
    (h15 : pre.length + 2 + am.tail.length ≤ 15) :
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))).run
        (afterFetches (beforeFetch s) (pre.length + 3)) =
      (.ok (am.offset (beforeFetch s), ctxSegment ctx am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: am.modrm reg :: (am.tail ++ rest)) := hcode
  refine effectiveAddress_run_seg (beforeFetch s) (pre.length + 3) h.fetchReady h.cpu.ds h.cpu.ss
    am hv ctx hctx hc hlow (pre.length + 2) (fun j hj => ?_) (by simp; omega) h15
  rw [getElem?_pre_tail, List.getElem?_append_left hj]

/-- `memAlu_ea_seg` at address size 32 (an address-size prefix): `Effective_Address` returns
`am.offset32` (`handleRIPRelativeAddress_addrMode32_run` turns it into `am.addr32`). -/
theorem memAlu_ea32_seg [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (op : UInt8) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (rest : List UInt8)
    (ctx : Instruction_Context) (hctx : SegAddrContext ctx am)
    (hcode : BytesAt s s.RIP (pre ++ op :: am.modrm reg :: (am.tail ++ rest)))
    (hlow : s.RIP.toNat + (pre ++ op :: am.modrm reg :: (am.tail ++ rest)).length ≤ 2^32)
    (h15 : pre.length + 2 + am.tail.length ≤ 15) :
    (Effective_Address 32 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)))).run
        (afterFetches (beforeFetch s) (pre.length + 3)) =
      (.ok (am.offset32 (beforeFetch s), ctxSegment ctx am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: am.modrm reg :: (am.tail ++ rest)) := hcode
  refine effectiveAddress32_run_seg (beforeFetch s) (pre.length + 3) h.fetchReady h.cpu.ds h.cpu.ss
    am hv ctx hctx hc hlow (pre.length + 2) (fun j hj => ?_) (by simp; omega) h15
  rw [getElem?_pre_tail, List.getElem?_append_left hj]

/-- Every state a step passes through before memory changes (after any number of fetches) has
the data-access facts. -/
theorem memAlu_dataReady [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) :=
  h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables

/-- What a locked access needs (`LockReady`) holds in every state a step passes through before
memory changes. -/
theorem memAlu_lockReady [Bindings] {s : RamState} {lin : BitVec 64} {len : Nat}
    (h : LockReady s lin len) (k : Nat) : LockReady (afterFetches (beforeFetch s) k) lin len :=
  h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The address after the ModRM tail and the immediate byte: `next + 1`. -/
theorem add_tail_imm (r : BitVec 64) (a : Nat) :
    BitVec.add (BitVec.add r (BitVec.ofNat 64 a)) 1#64 = BitVec.add r (BitVec.ofNat 64 (a + 1)) :=
  add_ofNat_add r a 1

end X86Proofs
