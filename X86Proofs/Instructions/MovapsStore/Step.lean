import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Instructions.MovStore.Step
import X86Proofs.Instructions.MovapsStore.Decode
import X86Proofs.Instructions.MovapsStore.Form

/-!
# Layer 3: `movaps m128, xmm` step theorems

`0F 29 /r` with a memory destination (`mod ≠ 3`) given by an `AddrMode` `am`, optionally after a
REX prefix; `len` is the instruction length and the destination is
`am.addrAt s len = am.addr s (RIP + len)`:

- `movaps_m128_xmm_step`: `0F 29 modrm tail` (no prefix; e.g.
  `0F 29 44 24 10`, `movaps [rsp + 0x10], xmm0`), source registers 0–7, a shape that needs
  neither REX.X nor REX.B, `len = 3 + am.tail.length`.
- `movaps_m128_xmm_rex_step`: `rex 0F 29 modrm tail`, any of the 16 source registers (REX.R) and
  any shape (REX.X, REX.B as `am` needs; REX.W is ignored), `len = 4 + am.tail.length`.

Besides `ReadyToStep`, the step needs SSE enabled (`Prelude.SupportedSSE`), the 16 bytes at the
destination writable in place (`MemWritable`) and the destination 16-byte aligned (MOVAPS's
`Explicitly_Aligned` check). The result is `afterStep s len fun t => writeResult
(dataAccess t "store") (.mem addr) (src.read s) (RIP + len)`, the shape of the integer stores, so
preservation and frame come from `Program/ReadWrite/Store.lean`.

Behind an FS/GS segment-override prefix (`r : SegReg`, its segment ready): `movaps_m128_xmm_seg_step`
and `movaps_m128_xmm_rex_seg_step` (via `movaps_0F29_memory_run_seg`, any `SegAddrContext`) store
at the linear address `segBase (r.read s) + am.addrAt s len`, which must be 16-byte aligned.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
The decode and form of `… 0F 29 modrm tail` with `29` at offset `k` (after `k - 1` prefix bytes,
context `ctx`), for addressing shape `am` and source field `reg`: from the state after the prefix
scan, `Decode_Legacy_1` stores the `reg` XMM register (extended by `ctx`'s REX.R) at
`am.addrAt s len`, `len = k + 2 + am.tail.length`, with `Next_IP` = RIP + `len`.
-/
theorem movaps_0F29_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (haddr : ctx.address_size = 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext ctx am) (bytes : List UInt8) (k : Nat)
    (hk : k + 2 + am.tail.length ≤ 15) (hlen : bytes.length = k + 2 + am.tail.length)
    (h29 : bytes[k]? = some 0x29) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (halign : (am.addrAt s (k + 2 + am.tail.length)).toNat % 16 = 0)
    (hw : MemWritable s (am.addrAt s (k + 2 + am.tail.length)) 16) :
    let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult
        (dataAccess (afterFetches (beforeFetch s) (k + 2 + am.tail.length + 1)) "store")
        (.mem (am.addrAt s (k + 2 + am.tail.length)) : Operand 128) (src.read s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length)))) := by
  intro src
  have hdecode := decodeLegacy1_run_of_29_memory s h hsse ctx hrex2 hosz (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) h29 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am hv
    ctx hctx hc hlow (k + 2) htail (by omega) (by omega)
  rw [show k + 3 + am.tail.length = k + 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 ctx am.mod am.rm 1
      (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (k + 2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (k + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hsse' : Prelude.SupportedSSE Bindings.processor t :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsse
  have haddr' : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length))) =
      am.addrAt s (k + 2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length)))
  rw [haddr'] at hrip
  rw [movaps_m_xmm_form _ t _ _ _ _ _ haddr hrep hlock hosz _ _ _ _ _ hea hrip ht hmode hsse' halign
    (hw.of_external_eq rfl)] at hdecode
  refine hdecode.trans ?_
  dsimp only
  rw [show (Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t =
    src.read s from (Operand.read_afterFetches _ _ _).trans (Operand.read_beforeFetch _ _)]

/-- `movaps_0F29_memory_run` with any segment prefix (`SegAddrContext`): the store is at
`segAddr ctx (am.addrAt s len)`, the operand's linear address. -/
theorem movaps_0F29_memory_run_seg [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (haddr : ctx.address_size = 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext ctx am) (bytes : List UInt8) (k : Nat)
    (hk : k + 2 + am.tail.length ≤ 15) (hlen : bytes.length = k + 2 + am.tail.length)
    (h29 : bytes[k]? = some 0x29) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (halign : (segAddr ctx (am.addrAt s (k + 2 + am.tail.length))).toNat % 16 = 0)
    (hw : MemWritable s (segAddr ctx (am.addrAt s (k + 2 + am.tail.length))) 16) :
    let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult
        (dataAccess (afterFetches (beforeFetch s) (k + 2 + am.tail.length + 1)) "store")
        (.mem (segAddr ctx (am.addrAt s (k + 2 + am.tail.length))) : Operand 128) (src.read s)
        (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length)))) := by
  intro src
  have hdecode := decodeLegacy1_run_of_29_memory s h hsse ctx hrex2 hosz (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) h29 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run_seg (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am
    hv ctx hctx hc hlow (k + 2) htail (by omega) (by omega)
  rw [show k + 3 + am.tail.length = k + 2 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 ctx am.mod am.rm 1
      (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), ctxSegment ctx am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (k + 2 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (k + 2 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.memory.tables
  have hsse' : Prelude.SupportedSSE Bindings.processor t :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      hsse
  have haddr' : am.addr (beforeFetch s)
      (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length))) =
      am.addrAt s (k + 2 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2 + am.tail.length)))
  rw [haddr'] at hrip
  rw [movaps_m_xmm_seg_form _ t _ _ _ _ _ haddr hrep hlock hosz _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) ht hmode hsse' halign (hw.of_external_eq rfl)] at hdecode
  refine hdecode.trans ?_
  dsimp only
  rw [show (Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t =
    src.read s from (Operand.read_afterFetches _ _ _).trans (Operand.read_beforeFetch _ _)]

/--
Layer 3 for `movaps m128, xmm` (`0F 29 /r`, no prefix, `mod ≠ 3`), source registers 0–7, for an
addressing shape `am` that needs neither REX.X nor REX.B: the instruction `0F, 29, am.modrm reg,
am.tail`, `len = 3 + am.tail.length` bytes. If the machine is ready to step with SSE enabled, the
instruction is at RIP below 4 GiB, and the 16 bytes at `am.addrAt s len` are 16-byte aligned
and can be written in place, one `step` stores the `reg` XMM register there, with
`Next_IP` = RIP + `len`.
-/
theorem movaps_m128_xmm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: 0x29 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (halign : (am.addrAt s (3 + am.tail.length)).toNat % 16 = 0)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 16) :
    let src : Operand 128 := .xmm (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 128)
        (src.read s) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro src
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (0x0F :: 0x29 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hrun := movaps_0F29_memory_run s h hsse (legacyContext s.DS) rfl rfl rfl rfl rfl reg am hv
    (AddrContext.legacy _ am hx hb) _ 1 (by omega) (by simp; omega) rfl rfl
    (fun j _ => by rw [show 1 + 2 + j = 3 + j by omega]; exact getElem?_cons3 _ _ _ _ j)
    hcode hlow' halign hw
  rw [show 1 + 2 + am.tail.length = 3 + am.tail.length by omega] at hrun
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x29 _ ⟨by decide, by decide⟩ hcode hlow' hrun
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
Layer 3 for `movaps m128, xmm` after a REX prefix (`rex 0F 29 /r`, `mod ≠ 3`), any of the 16
source registers (REX.R extends `reg`) and any addressing shape `am` (REX.X and REX.B as `am`
needs): the instruction `rex, 0F, 29, am.modrm reg, am.tail`, `len = 4 + am.tail.length` bytes.
As `movaps_m128_xmm_step` otherwise.
-/
theorem movaps_m128_xmm_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (halign : (am.addrAt s (4 + am.tail.length)).toNat % 16 = 0)
    (hw : MemWritable s (am.addrAt s (4 + am.tail.length)) 16) :
    let src : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (4 + am.tail.length)) : Operand 128)
        (src.read s) (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro src
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hrun := movaps_0F29_memory_run s h hsse (rexContext s.DS rex.toBitVec) rfl rfl rfl rfl rfl
    reg am hv (AddrContext.rex _ _ am hx hb) _ 2 (by omega) (by simp; omega) rfl rfl
    (fun j _ => by
      rw [show 2 + 2 + j = 3 + j + 1 by omega, List.getElem?_cons_succ]
      exact getElem?_cons3 _ _ _ _ j)
    hcode hlow' halign hw
  rw [show 2 + 2 + am.tail.length = 4 + am.tail.length by omega] at hrun
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x29 _ hrex ⟨by decide, by decide⟩ hcode hlow' hrun
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
Layer 3 for `movaps m128, xmm` behind an FS/GS segment-override prefix (`64`/`65 0F 29 /r`,
`mod ≠ 3`; `r` the segment register, ready for data accesses), source registers 0–7 and a shape
needing no REX bit: as `movaps_m128_xmm_step`, storing at the linear address
`segBase (r.read s) + am.addrAt s len` (16-byte aligned), `len = 4 + am.tail.length`.
-/
theorem movaps_m128_xmm_seg_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (r : SegReg) (hseg : SegReady (r.read s))
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (r.prefixByte :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (halign : (segBase (r.read s) + am.addrAt s (4 + am.tail.length)).toNat % 16 = 0)
    (hw : MemWritable s (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) 16) :
    let src : Operand 128 := .xmm (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "store")
        (.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 128)
        (src.read s) (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro src
  have htl := am.tail_length_le
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) :=
    scanContext_seg_cons _ _ r [] noSegPrefix_nil
  have hlow' : s.RIP.toNat + (r.prefixByte :: 0x0F :: 0x29 :: am.modrm reg :: am.tail).length ≤
      2^32 := by
    simp only [List.length_cons]; omega
  have hrun := movaps_0F29_memory_run_seg s h hsse (scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte])
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) _ 2 (by omega)
    (by simp; omega) rfl rfl
    (fun j _ => by rw [show 2 + 2 + j = j + 1 + 1 + 1 + 1 by omega]; rfl) hcode hlow'
    (by rw [hsc, segAddr_withSeg]; exact halign) (by rw [hsc, segAddr_withSeg]; exact hw)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  have hstep := step_scan_legacy1 s _ h [r.prefixByte] 0x29 _ (scanPrefix_seg_cons r (by simp))
    ⟨by decide, by decide⟩ (by simp) hcode hlow' hrun
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

/--
Layer 3 for `movaps m128, xmm` behind an FS/GS segment-override prefix and a REX prefix
(`64`/`65 rex 0F 29 /r`, `mod ≠ 3`), any of the 16 source registers and any shape: as
`movaps_m128_xmm_rex_step`, storing at `segBase (r.read s) + am.addrAt s len`,
`len = 5 + am.tail.length`.
-/
theorem movaps_m128_xmm_rex_seg_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (r : SegReg) (hseg : SegReady (r.read s))
    (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (r.prefixByte :: rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32)
    (halign : (segBase (r.read s) + am.addrAt s (5 + am.tail.length)).toNat % 16 = 0)
    (hw : MemWritable s (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) 16) :
    let src : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (5 + am.tail.length) fun t =>
      writeResult (dataAccess t "store")
        (.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 128)
        (src.read s) (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length))))) := by
  intro src
  have htl := am.tail_length_le
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hrex.noSegPrefix noSegPrefix_nil),
      scanContext_rex _ _ hrex]
  have hlow' : s.RIP.toNat +
      (r.prefixByte :: rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hrun := movaps_0F29_memory_run_seg s h hsse
    (scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex])
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) _ 3 (by omega)
    (by simp; omega) rfl rfl
    (fun j _ => by rw [show 3 + 2 + j = j + 1 + 1 + 1 + 1 + 1 by omega]; rfl) hcode hlow'
    (by rw [hsc, segAddr_withSeg]; exact halign) (by rw [hsc, segAddr_withSeg]; exact hw)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  have hstep := step_scan_legacy1 s _ h [r.prefixByte, rex] 0x29 _
    (scanPrefix_seg_cons r (by simpa using hrex.scanPrefix)) ⟨by decide, by decide⟩ (by simp) hcode
    hlow' hrun (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

end X86Proofs
