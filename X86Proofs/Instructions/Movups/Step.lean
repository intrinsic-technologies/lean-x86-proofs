import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Instructions.MovLoad.Step
import X86Proofs.Instructions.Movups.Decode
import X86Proofs.Instructions.Movups.Form

/-!
# Layer 3: `movups xmm, m128` step theorems

`0F 10 /r` with a memory operand given by an `AddrMode` `am`, optionally after a REX prefix; `len`
is the instruction length and the operand's address is `am.addrAt s len = am.addr s
(RIP + len)` (relative to the instruction's end for a RIP-relative operand):

- `movups_xmm_m128_step`: `0F 10 modrm tail` (e.g. `0F 10 01`, `0F 10 49 10`), registers
  0–7 and an address needing no REX bit, `len = 3 + am.tail.length`.
- `movups_xmm_m128_rex_step`: `rex 0F 10 modrm tail` (e.g. `41 0F 10 04 0F`), any of the
  16 registers and any address, `len = 4 + am.tail.length`.

The result is `afterStep s len fun t => writeResult (dataAccess t "load") dst v (RIP + len)` with
`v` the 16 bytes at `am.addrAt s len` (no alignment requirement; they may cross a page).
Besides `ReadyToStep`, the step needs SSE enabled (`Prelude.SupportedSSE`). Preservation:
`ReadyToStep.afterStep_load_xmm` (`Program/ReadWrite/Sse.lean`).

`decode_sse_load_common` is the part shared with XORPS (`XorpsLoad/Step.lean`): the facts about
the state after the decoder, for an opcode at offset `k`.

Behind an FS/GS segment-override prefix (`r : SegReg`, its segment ready, `SegReady`):
`movups_xmm_m128_seg_step` (`r.prefixByte 0F 10 modrm tail`) and `movups_xmm_m128_rex_seg_step`
(`r.prefixByte rex 0F 10 modrm tail`) read at the linear address `segBase (r.read s) +
am.addrAt s len`; `decode_sse_load_common_seg` and `movups_0F10_memory_run_seg` are their shared
parts (any `SegAddrContext`, the opcode at offset `k ≤ 3`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem getElem?_cons4 (a b c d : UInt8) (l : List UInt8) (j : Nat) :
    (a :: b :: c :: d :: l)[4 + j]? = l[j]? := by
  rw [show 4 + j = j + 1 + 1 + 1 + 1 by omega]
  rfl

/--
What an SSE load form (`0F op /r`, memory operand) needs from the state the opcode decoder hands
it, for an instruction `bytes` at RIP with the opcode at offset `k` and `am.tail` at `k + 2`
(`len = k + 2 + am.tail.length` bytes): the address computation's result, and the facts about the
state `t` after it.
-/
theorem decode_sse_load_common [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext ctx am) (bytes : List UInt8) (k len : Nat)
    (hk : k ≤ 2) (hlen : k + 2 + am.tail.length = len) (hbytes : bytes.length = len)
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    let t := afterFetches (beforeFetch s) (len + 1)
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run
        (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 len), am.isRip, am.baseUsesRsp), t) ∧
    Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
        (BitVec.add s.RIP (BitVec.ofNat 64 len)) = .ok (am.addrAt s len) ∧
    DataReady t ∧ In64BitMode t ∧ Prelude.SupportedSSE Bindings.processor t := by
  intro t
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am hv
    ctx hctx hc hlow (k + 2) htail (by omega) (by have := am.tail_length_le; omega)
  rw [show k + 3 + am.tail.length = len + 1 by omega, show k + 2 + am.tail.length = len by omega]
    at hea
  have hst : SameControls s t := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 len)) =
      am.addrAt s len := AddrMode.addr_of_gpr rfl _
  refine ⟨hea, ?_, h.dataReady.of_sameControls hst rfl rfl rfl rfl rfl h.memory.tables,
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma, SupportedSSE.of_sameControls hst hsse⟩
  rw [← haddr]
  exact handleRIPRelativeAddress_addrMode_run am (beforeFetch s) _

/-- `decode_sse_load_common` with any segment prefix (`SegAddrContext`), for an opcode at offset
`k ≤ 3` (an FS/GS prefix and a REX prefix before `0F`): the address computation returns the segment
`ctxSegment ctx am.isStack`. -/
theorem decode_sse_load_common_seg [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext ctx am) (bytes : List UInt8)
    (k len : Nat) (hk : k ≤ 3) (hlen : k + 2 + am.tail.length = len) (hbytes : bytes.length = len)
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    let t := afterFetches (beforeFetch s) (len + 1)
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run
        (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), ctxSegment ctx am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 len), am.isRip, am.baseUsesRsp), t) ∧
    Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
        (BitVec.add s.RIP (BitVec.ofNat 64 len)) = .ok (am.addrAt s len) ∧
    DataReady t ∧ In64BitMode t ∧ Prelude.SupportedSSE Bindings.processor t := by
  intro t
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run_seg (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am
    hv ctx hctx hc hlow (k + 2) htail (by omega) (by have := am.tail_length_le; omega)
  rw [show k + 3 + am.tail.length = len + 1 by omega, show k + 2 + am.tail.length = len by omega]
    at hea
  have hst : SameControls s t := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 len)) =
      am.addrAt s len := AddrMode.addr_of_gpr rfl _
  refine ⟨hea, ?_, h.dataReady.of_sameControls hst rfl rfl rfl rfl rfl h.memory.tables,
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma, SupportedSSE.of_sameControls hst hsse⟩
  rw [← haddr]
  exact handleRIPRelativeAddress_addrMode_run am (beforeFetch s) _

/-- The common part of the two MOVUPS step theorems: `Decode_Legacy_1` from the scan's state, for
`10` at offset `k`, runs the whole instruction. -/
theorem movups_0F10_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext ctx am) (bytes : List UInt8) (k len : Nat)
    (hk : k ≤ 2) (hlen : k + 2 + am.tail.length = len) (hbytes : bytes.length = len)
    (h10 : bytes[k]? = some 0x10) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hread : MemReadable s (am.addrAt s len) 16) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (dataAccess (afterFetches (beforeFetch s) (len + 1)) "load")
        (.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg))
        ((Operand.mem (am.addrAt s len) : Operand 128).read
          (afterFetches (beforeFetch s) (len + 1)))
        (BitVec.add s.RIP (BitVec.ofNat 64 len))) := by
  have hdecode := decodeLegacy1_run_of_10_memory s h hsse ctx hrex2 hosz hrep (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) h10 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  obtain ⟨hea, hrip, ht, hmode, hsse'⟩ :=
    decode_sse_load_common s h hsse ctx am hv hctx bytes k len hk hlen hbytes htail hcode hlow
  rw [movups_xmm_m_form _ _ _ _ _ _ _ haddr hrep hlock hosz hvex hevex _ _ _ _ _ hea hrip ht hmode
    hsse' hread.low hread.mem] at hdecode
  exact hdecode

/-- `movups_0F10_memory_run` with any segment prefix (`SegAddrContext`), for `10` at offset
`k ≤ 3`: the read is at `segAddr ctx (am.addrAt s len)`, the operand's linear address. -/
theorem movups_0F10_memory_run_seg [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hctx : SegAddrContext ctx am) (bytes : List UInt8)
    (k len : Nat) (hk : k ≤ 3) (hlen : k + 2 + am.tail.length = len)
    (hbytes : bytes.length = len)
    (h10 : bytes[k]? = some 0x10) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hread : MemReadable s (segAddr ctx (am.addrAt s len)) 16) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (dataAccess (afterFetches (beforeFetch s) (len + 1)) "load")
        (.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg))
        ((Operand.mem (segAddr ctx (am.addrAt s len)) : Operand 128).read
          (afterFetches (beforeFetch s) (len + 1)))
        (BitVec.add s.RIP (BitVec.ofNat 64 len))) := by
  have hdecode := decodeLegacy1_run_of_10_memory s h hsse ctx hrex2 hosz hrep (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) h10 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  obtain ⟨hea, hrip, ht, hmode, hsse'⟩ :=
    decode_sse_load_common_seg s h hsse ctx am hv hctx bytes k len hk hlen hbytes htail hcode hlow
  rw [movups_xmm_m_seg_form _ _ _ _ _ _ _ haddr hrep hlock hosz hvex hevex _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) ht hmode hsse' hread.low hread.mem] at hdecode
  exact hdecode

/--
Layer 3 for `movups xmm, m128` (`0F 10 /r`, no prefix, `mod ≠ 3`), registers 0–7 and an address
needing neither REX.X nor REX.B. If the machine is ready to step with SSE enabled, the bytes
`0F 10 modrm tail` are at RIP below 4 GiB, and the 16 bytes at the operand's address lie below
4 GiB and are present in RAM, one `step` loads them into the `reg` register, with `Next_IP` =
RIP + `3 + am.tail.length`.
-/
theorem movups_xmm_m128_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: 0x10 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (3 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 128).read t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (0x0F :: 0x10 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := movups_0F10_memory_run s h hsse (legacyContext s.DS) rfl rfl rfl rfl rfl rfl
    rfl reg am hv (AddrContext.legacy _ am hx hb) _ 1 (3 + am.tail.length) (by decide)
    (by omega) (by simp; omega) rfl rfl (fun j _ => getElem?_cons3 _ _ _ _ j) hcode hlow' hread
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x10 _ ⟨by decide, by decide⟩ hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
Layer 3 for `movups xmm, m128` after a REX prefix (`rex 0F 10 /r`, `mod ≠ 3`), any of the 16
registers (REX.R extends `reg`) and any addressing shape `am` (REX.X and REX.B as `am` needs). As
`movups_xmm_m128_step` otherwise, with `Next_IP` = RIP + `4 + am.tail.length`.
-/
theorem movups_xmm_m128_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (4 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        ((Operand.mem (am.addrAt s (4 + am.tail.length)) : Operand 128).read t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := movups_0F10_memory_run s h hsse (rexContext s.DS rex.toBitVec) rfl rfl rfl
    rfl rfl rfl rfl reg am hv (AddrContext.rex _ _ am hx hb) _ 2 (4 + am.tail.length) (by decide)
    (by omega) (by simp; omega) rfl rfl (fun j _ => getElem?_cons4 _ _ _ _ _ j) hcode hlow' hread
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x10 _ hrex ⟨by decide, by decide⟩ hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

/--
Layer 3 for `movups xmm, m128` behind an FS/GS segment-override prefix (`64 0F 10 /r` or
`65 0F 10 /r`, `mod ≠ 3`; `r` the segment register, ready for data accesses), registers 0–7 and
an address needing no REX bit: as `movups_xmm_m128_step`, reading the 16 bytes at the linear
address `segBase (r.read s) + am.addrAt s len`, `len = 4 + am.tail.length`.
-/
theorem movups_xmm_m128_seg_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (r : SegReg) (hseg : SegReady (r.read s))
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (r.prefixByte :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        ((Operand.mem (segBase (r.read s) + am.addrAt s (4 + am.tail.length)) : Operand 128).read
          t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) :=
    scanContext_seg_cons _ _ r [] noSegPrefix_nil
  have hlow' : s.RIP.toNat + (r.prefixByte :: 0x0F :: 0x10 :: am.modrm reg :: am.tail).length ≤
      2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := movups_0F10_memory_run_seg s h hsse (scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte])
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) _ 2 (4 + am.tail.length)
    (by decide) (by omega) (by simp; omega) rfl rfl (fun j _ => getElem?_cons4 _ _ _ _ _ j) hcode
    hlow' (by rw [hsc, segAddr_withSeg]; exact hread)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  have hstep := step_scan_legacy1 s _ h [r.prefixByte] 0x10 _ (scanPrefix_seg_cons r (by simp))
    ⟨by decide, by decide⟩ (by simp) hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

/--
Layer 3 for `movups xmm, m128` behind an FS/GS segment-override prefix and a REX prefix
(`64 rex 0F 10 /r` or `65 rex 0F 10 /r`, `mod ≠ 3`), any of the 16 registers and any addressing
shape: as `movups_xmm_m128_rex_step`, reading at `segBase (r.read s) + am.addrAt s len`,
`len = 5 + am.tail.length`.
-/
theorem movups_xmm_m128_rex_seg_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (r : SegReg) (hseg : SegReady (r.read s))
    (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (r.prefixByte :: rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) 16) :
    let dst : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (5 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        ((Operand.mem (segBase (r.read s) + am.addrAt s (5 + am.tail.length)) : Operand 128).read
          t)
        (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length))))) := by
  intro dst
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hrex.noSegPrefix noSegPrefix_nil),
      scanContext_rex _ _ hrex]
  have hlow' : s.RIP.toNat +
      (r.prefixByte :: rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := movups_0F10_memory_run_seg s h hsse
    (scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex])
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) _ 3 (5 + am.tail.length)
    (by decide) (by omega) (by simp; omega) rfl rfl
    (fun j _ => by rw [show 3 + 2 + j = j + 1 + 1 + 1 + 1 + 1 by omega]; rfl) hcode hlow'
    (by rw [hsc, segAddr_withSeg]; exact hread)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  have hstep := step_scan_legacy1 s _ h [r.prefixByte, rex] 0x10 _
    (scanPrefix_seg_cons r (by simpa using hrex.scanPrefix)) ⟨by decide, by decide⟩ (by simp) hcode
    hlow' hdecode (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

end X86Proofs
