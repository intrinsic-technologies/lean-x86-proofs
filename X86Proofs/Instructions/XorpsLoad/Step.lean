import X86Proofs.Instructions.Movups.Step
import X86Proofs.Instructions.XorpsLoad.Decode
import X86Proofs.Instructions.XorpsLoad.Form

/-!
# Layer 3: `xorps xmm, m128` step theorems

`0F 57 /r` with a memory operand given by an `AddrMode` `am`, optionally after a REX prefix, laid
out as MOVUPS (`Movups/Step.lean`); the operand's address is `am.addrAt s len`:

- `xorps_xmm_m128_step`: `0F 57 modrm tail` (e.g. `0F 57 44 24 10`, `0F 57 44 0C 10`),
  registers 0–7 and an address needing no REX bit, `len = 3 + am.tail.length`.
- `xorps_xmm_m128_rex_step`: `rex 0F 57 modrm tail`, any of the 16 registers and any address,
  `len = 4 + am.tail.length`.

The result is `afterStep s len fun t => writeResult (dataAccess t "load") dst (dst.read t ^^^ v)
(RIP + len)` with `v` the 16 bytes at `am.addrAt s len`, which must be 16-byte aligned
(`Explicitly_Aligned`, else #GP). Preservation: `ReadyToStep.afterStep_load_xmm`.

Behind an FS/GS segment-override prefix (`r : SegReg`, its segment ready): `xorps_xmm_m128_seg_step`
and `xorps_xmm_m128_rex_seg_step` (via `xorps_0F57_memory_run_seg`, any `SegAddrContext`) read at
the linear address `segBase (r.read s) + am.addrAt s len`, which must be 16-byte aligned.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The common part of the two XORPS step theorems: `Decode_Legacy_1` from the scan's state, for
`57` at offset `k` with a memory ModRM, runs the whole instruction. -/
theorem xorps_0F57_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext ctx am) (bytes : List UInt8) (k len : Nat)
    (hk : k ≤ 2) (hlen : k + 2 + am.tail.length = len) (hbytes : bytes.length = len)
    (h57 : bytes[k]? = some 0x57) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (halign : (am.addrAt s len).toNat % 16 = 0)
    (hread : MemReadable s (am.addrAt s len) 16) :
    let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (dataAccess (afterFetches (beforeFetch s) (len + 1)) "load") dst
        (dst.read (afterFetches (beforeFetch s) (len + 1)) ^^^
          (Operand.mem (am.addrAt s len) : Operand 128).read
            (afterFetches (beforeFetch s) (len + 1)))
        (BitVec.add s.RIP (BitVec.ofNat 64 len))) := by
  intro dst
  have hdecode := decodeLegacy1_run_of_57_memory s h hsse ctx hrex2 hosz (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) h57 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  obtain ⟨hea, hrip, ht, hmode, hsse'⟩ :=
    decode_sse_load_common s h hsse ctx am hv hctx bytes k len hk hlen hbytes htail hcode hlow
  rw [xorps_xmm_m_form _ _ _ _ _ _ _ haddr hrep hlock hosz hvex hevex _ _ _ _ _ hea hrip ht hmode
    hsse' halign hread.low hread.mem] at hdecode
  exact hdecode

/-- `xorps_0F57_memory_run` with any segment prefix (`SegAddrContext`), for `57` at offset
`k ≤ 3`: the read is at `segAddr ctx (am.addrAt s len)`, the operand's linear address, which must
be 16-byte aligned. -/
theorem xorps_0F57_memory_run_seg [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext ctx am) (bytes : List UInt8)
    (k len : Nat) (hk : k ≤ 3) (hlen : k + 2 + am.tail.length = len)
    (hbytes : bytes.length = len)
    (h57 : bytes[k]? = some 0x57) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (halign : (segAddr ctx (am.addrAt s len)).toNat % 16 = 0)
    (hread : MemReadable s (segAddr ctx (am.addrAt s len)) 16) :
    let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (dataAccess (afterFetches (beforeFetch s) (len + 1)) "load") dst
        (dst.read (afterFetches (beforeFetch s) (len + 1)) ^^^
          (Operand.mem (segAddr ctx (am.addrAt s len)) : Operand 128).read
            (afterFetches (beforeFetch s) (len + 1)))
        (BitVec.add s.RIP (BitVec.ofNat 64 len))) := by
  intro dst
  have hdecode := decodeLegacy1_run_of_57_memory s h hsse ctx hrex2 hosz (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) h57 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  obtain ⟨hea, hrip, ht, hmode, hsse'⟩ :=
    decode_sse_load_common_seg s h hsse ctx am hv hctx bytes k len hk hlen hbytes htail hcode hlow
  rw [xorps_xmm_m_seg_form _ _ _ _ _ _ _ haddr hrep hlock hosz hvex hevex _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) ht hmode hsse' halign hread.low hread.mem] at hdecode
  exact hdecode

/--
Layer 3 for `xorps xmm, m128` (`0F 57 /r`, no prefix, `mod ≠ 3`), registers 0–7 and an address
needing neither REX.X nor REX.B. If the machine is ready to step with SSE enabled, the bytes
`0F 57 modrm tail` are at RIP below 4 GiB, and the 16 bytes at the operand's address are 16-byte
aligned, lie below 4 GiB and are present in RAM, one `step` xors them into the `reg` register,
with `Next_IP` = RIP + `3 + am.tail.length`.
-/
theorem xorps_xmm_m128_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: 0x57 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (halign : (am.addrAt s (3 + am.tail.length)).toNat % 16 = 0)
    (hread : MemReadable s (am.addrAt s (3 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (dst.read t ^^^ (Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 128).read t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (0x0F :: 0x57 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := xorps_0F57_memory_run s h hsse (legacyContext s.DS) rfl rfl rfl rfl rfl rfl
    rfl reg am hv (AddrContext.legacy _ am hx hb) _ 1 (3 + am.tail.length) (by decide)
    (by omega) (by simp; omega) rfl rfl (fun j _ => getElem?_cons3 _ _ _ _ j) hcode hlow' halign
    hread
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x57 _ ⟨by decide, by decide⟩ hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
Layer 3 for `xorps xmm, m128` after a REX prefix (`rex 0F 57 /r`, `mod ≠ 3`), any of the 16
registers (REX.R extends `reg`) and any addressing shape `am` (REX.X and REX.B as `am` needs). As
`xorps_xmm_m128_step` otherwise, with `Next_IP` = RIP + `4 + am.tail.length`.
-/
theorem xorps_xmm_m128_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (halign : (am.addrAt s (4 + am.tail.length)).toNat % 16 = 0)
    (hread : MemReadable s (am.addrAt s (4 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (dst.read t ^^^ (Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 128).read t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := xorps_0F57_memory_run s h hsse (rexContext s.DS rex.toBitVec) rfl rfl rfl
    rfl rfl rfl rfl reg am hv (AddrContext.rex _ _ am hx hb) _ 2 (4 + am.tail.length) (by decide)
    (by omega) (by simp; omega) rfl rfl (fun j _ => getElem?_cons4 _ _ _ _ _ j) hcode hlow'
    halign hread
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x57 _ hrex ⟨by decide, by decide⟩ hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
Layer 3 for `xorps xmm, m128` behind an FS/GS segment-override prefix (`64`/`65 0F 57 /r`,
`mod ≠ 3`; `r` the segment register, ready for data accesses), registers 0–7 and an address needing
no REX bit: as `xorps_xmm_m128_step`, the 16 bytes at the linear address
`segBase (r.read s) + am.addrAt s len` (16-byte aligned), `len = 4 + am.tail.length`.
-/
theorem xorps_xmm_m128_seg_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (r : SegReg) (hseg : SegReady (r.read s))
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (r.prefixByte :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (halign : (segBase (r.read s) + am.addrAt s (4 + am.tail.length)).toNat % 16 = 0)
    (hread : MemReadable s (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (dst.read t ^^^ (Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) :
          Operand 128).read t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) :=
    scanContext_seg_cons _ _ r [] noSegPrefix_nil
  have hlow' : s.RIP.toNat + (r.prefixByte :: 0x0F :: 0x57 :: am.modrm reg :: am.tail).length ≤
      2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := xorps_0F57_memory_run_seg s h hsse (scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte])
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) _ 2 (4 + am.tail.length)
    (by decide) (by omega) (by simp; omega) rfl rfl (fun j _ => getElem?_cons4 _ _ _ _ _ j) hcode
    hlow' (by rw [hsc, segAddr_withSeg]; exact halign) (by rw [hsc, segAddr_withSeg]; exact hread)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  have hstep := step_scan_legacy1 s _ h [r.prefixByte] 0x57 _ (scanPrefix_seg_cons r (by simp))
    ⟨by decide, by decide⟩ (by simp) hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

/--
Layer 3 for `xorps xmm, m128` behind an FS/GS segment-override prefix and a REX prefix
(`64`/`65 rex 0F 57 /r`, `mod ≠ 3`), any of the 16 registers and any addressing shape: as
`xorps_xmm_m128_rex_step`, the 16 bytes at `segBase (r.read s) + am.addrAt s len`,
`len = 5 + am.tail.length`.
-/
theorem xorps_xmm_m128_rex_seg_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (r : SegReg) (hseg : SegReady (r.read s))
    (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (r.prefixByte :: rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32)
    (halign : (segBase (r.read s) + am.addrAt s (5 + am.tail.length)).toNat % 16 = 0)
    (hread : MemReadable s (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (5 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (dst.read t ^^^ (Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) :
          Operand 128).read t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length))))) := by
  intro dst
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hrex.noSegPrefix noSegPrefix_nil),
      scanContext_rex _ _ hrex]
  have hlow' : s.RIP.toNat +
      (r.prefixByte :: rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := xorps_0F57_memory_run_seg s h hsse
    (scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex])
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) _ 3 (5 + am.tail.length)
    (by decide) (by omega) (by simp; omega) rfl rfl
    (fun j _ => by rw [show 3 + 2 + j = j + 1 + 1 + 1 + 1 + 1 by omega]; rfl) hcode hlow'
    (by rw [hsc, segAddr_withSeg]; exact halign) (by rw [hsc, segAddr_withSeg]; exact hread)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  have hstep := step_scan_legacy1 s _ h [r.prefixByte, rex] 0x57 _
    (scanPrefix_seg_cons r (by simpa using hrex.scanPrefix)) ⟨by decide, by decide⟩ (by simp) hcode
    hlow' hdecode (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

end X86Proofs
