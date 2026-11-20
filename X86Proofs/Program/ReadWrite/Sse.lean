import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Step.Sse
import X86Proofs.Program.Compose

/-!
# XMM writes: what a step that writes an XMM register keeps

The SSE forms with an XMM destination end in `writeResult t (.xmm r) v nextIP` (register source,
e.g. XORPS) or `writeResult (dataAccess t "load") (.xmm r) v nextIP` (memory source, e.g. MOVUPS
and XORPS with `m128`). After such a step, as for the general-purpose register forms
(`Program/ReadWrite/WriteResult.lean`, `Program/ReadWrite/Load.lean`):

- RIP is `nextIP`: the general `afterStep_writeResult_rip` and `afterStep_load_rip`;
- `Operand.read_afterStep_writeResult_xmm`, `Operand.read_afterStep_load_xmm`: the register reads
  the value written;
- `ReadyToStep.afterStep_writeResult_xmm`, `ReadyToStep.afterStep_load_xmm`: the state is ready to
  step again;
- `AgreesExcept.afterStep_writeResult_xmm`, `AgreesExcept.afterStep_load_xmm`: only that XMM
  register (its low 128 bits) and RIP change.

`SsePre p s`: the precondition of an SSE register triple at `p`: RIP = `p` and SSE enabled
(`Prelude.SupportedSSE`, `Step/Sse.lean`). With a memory operand:
- `SseAlignedStorePre`: an aligned 128-bit store's (`StorePre`, SSE enabled, address a multiple
  of 16);
- `SseLoadPre p addr`: a 128-bit load's, unaligned (`Explicitly_Unaligned`, MOVUPS): SSE enabled
  and the 16 bytes at the operand's address readable (`MemReadable`: below 4 GiB and present in
  RAM; they may cross a page);
- `SseAlignedLoadPre p addr`: also the address a multiple of 16 (`Explicitly_Aligned`, e.g.
  XORPS: a misaligned operand raises #GP).

The SSE2 forms (`66 0F …`: PADDB, PAND, ANDPD, …) are decoded only if CPUID also reports SSE2:
`Sse2Pre p` and `Sse2AlignedLoadPre p addr` add that to `SsePre` and `SseAlignedLoadPre`
(`SsePre.sse2_of_holds`: every effect keeps it).

The moves between an XMM register and memory (MOVUPD, MOVSS, MOVLPS, MOVQ, …) read or write
`len` bytes, 16, 8 or 4, with no alignment requirement (`Explicitly_Unaligned`, or the integer
forms' `Normal_Alignment`, which checks only with alignment checking on, `CR0.AM = 0` here):
- `SseLoadNPre p addr len`, `Sse2LoadNPre p addr len`: a load of `len` bytes (as `SseLoadPre`,
  which is the 16-byte case);
- `SseStoreNPre p codeLen addr len`, `Sse2StoreNPre p codeLen addr len`: a store of `len` bytes
  (`StorePre` and SSE enabled; the bytes may cross a page, as every store's here);
- `Sse2AlignedStorePre p codeLen addr`: `SseAlignedStorePre` and SSE2 (MOVAPD, MOVDQA, and the
  non-temporal MOVNTPD, MOVNTDQ);
- `Sse2GprStorePre p codeLen addr len`: `StorePre` and SSE2 reported, without SSE enabled
  (MOVNTI, whose source is a general-purpose register).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The precondition of an SSE triple at `p` with no memory operand: RIP = `p`, and SSE is
enabled (`Prelude.SupportedSSE`: CPUID reports SSE, `CR0.EM = CR0.TS = 0`,
`CR4.OSFXSR = CR4.OSXMMEXCPT = 1`). -/
structure SsePre [Bindings] (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  sse : Prelude.SupportedSSE Bindings.processor s

/-- The precondition of an aligned 128-bit SSE store triple at `p` (`movaps m128, xmm`) for an
instruction of `codeLen` bytes writing the 16 bytes at `addr s`: `StorePre` (RIP = `p`, the bytes
writable in place and apart from the instruction), SSE enabled, and the address a multiple of 16
(the `Explicitly_Aligned` check; such a write never crosses a page). -/
structure SseAlignedStorePre [Bindings] (p : BitVec 64) (codeLen : Nat)
    (addr : RamState → BitVec 64) (s : RamState) : Prop where
  store : StorePre p codeLen addr 16 s
  sse : Prelude.SupportedSSE Bindings.processor s
  align : (addr s).toNat % 16 = 0

/-- The precondition of an unaligned SSE load triple at `p`: RIP = `p`, SSE enabled, and the 16
bytes at the operand's address (a function of the start state, e.g.
`fun s => am.addr s (p + instruction length)`) can be read. -/
structure SseLoadPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  sse : Prelude.SupportedSSE Bindings.processor s
  read : MemReadable s (addr s) 16

/-- The precondition of an aligned SSE load triple at `p`: `SseLoadPre`, and the operand's
address is a multiple of 16. -/
structure SseAlignedLoadPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64)
    (s : RamState) : Prop extends SseLoadPre p addr s where
  aligned : (addr s).toNat % 16 = 0

/-- The precondition of an SSE2 triple at `p` with no memory operand: `SsePre p`, and CPUID
reports SSE2 (which the opcode decoders check before they select a `66 0F …` SSE2 form). -/
structure Sse2Pre [Bindings] (p : BitVec 64) (s : RamState) : Prop extends SsePre p s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- The precondition of an aligned SSE2 load triple at `p` (`66 0F … /r` with an `m128` operand
read with `Explicitly_Aligned`): `SseAlignedLoadPre p addr`, and CPUID reports SSE2. -/
structure Sse2AlignedLoadPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64)
    (s : RamState) : Prop extends SseAlignedLoadPre p addr s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- The precondition of an SSE load triple at `p` reading `len` bytes (`SseLoadPre` for any
width: MOVSS `m32`, MOVLPS `m64`, …): RIP = `p`, SSE enabled, and the `len` bytes at the
operand's address readable. No alignment requirement; they may cross a page. -/
structure SseLoadNPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  sse : Prelude.SupportedSSE Bindings.processor s
  read : MemReadable s (addr s) len

/-- `SseLoadNPre`, and CPUID reports SSE2 (the `66` and SSE2 `F3` loads: MOVUPD, MOVDQU,
MOVLPD, MOVQ, MOVD, …). -/
structure Sse2LoadNPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop extends SseLoadNPre p addr len s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- The precondition of an SSE store triple at `p` for an instruction of `codeLen` bytes writing
the `len` bytes at `addr s`, with no alignment requirement (MOVUPS `m128`, MOVSS `m32`, MOVLPS
`m64`, …): `StorePre` (RIP = `p`, the bytes writable in place and apart from the instruction; they
may cross a page) and SSE enabled. -/
structure SseStoreNPre [Bindings] (p : BitVec 64) (codeLen : Nat)
    (addr : RamState → BitVec 64) (len : Nat) (s : RamState) : Prop where
  store : StorePre p codeLen addr len s
  sse : Prelude.SupportedSSE Bindings.processor s

/-- `SseStoreNPre`, and CPUID reports SSE2 (MOVUPD, MOVDQU, MOVLPD, MOVQ, MOVD, … stores). -/
structure Sse2StoreNPre [Bindings] (p : BitVec 64) (codeLen : Nat)
    (addr : RamState → BitVec 64) (len : Nat) (s : RamState) : Prop
    extends SseStoreNPre p codeLen addr len s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- `SseAlignedStorePre`, and CPUID reports SSE2 (the aligned SSE2 stores MOVAPD, MOVDQA). -/
structure Sse2AlignedStorePre [Bindings] (p : BitVec 64) (codeLen : Nat)
    (addr : RamState → BitVec 64) (s : RamState) : Prop
    extends SseAlignedStorePre p codeLen addr s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- The precondition of a store triple of an SSE2 instruction with a general-purpose source
(MOVNTI `m32/m64, r32/r64`), at `p` for an instruction of `codeLen` bytes writing the `len` bytes
at `addr s`: `StorePre`, and CPUID reports SSE2 (the opcode decoder checks it). No XMM state is
touched, so SSE need not be enabled. -/
structure Sse2GprStorePre [Bindings] (p : BitVec 64) (codeLen : Nat)
    (addr : RamState → BitVec 64) (len : Nat) (s : RamState) : Prop where
  store : StorePre p codeLen addr len s
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- An XMM write keeps bits 128–511 of every ZMM register. -/
theorem zmm_map_xmmClear_write {n : Nat} (z : Vector (BitVec 512) n) (i : Fin n)
    (v : BitVec 128) :
    (z.set i (xmmMerge v z[i])).map xmmClear = z.map xmmClear := by
  rw [Vector.map_set, xmmClear_xmmMerge, Fin.getElem_fin, ← Vector.getElem_map (f := xmmClear),
    Vector.set_getElem_self]

/-- An XMM write of `r` keeps every XMM component but `r` and every other component. -/
theorem AgreesExcept.write_xmm (t : RamState) (r : BitVec 5) (v : BitVec 128) :
    AgreesExcept [.xmm r] t ((Operand.xmm r : Operand 128).write t v) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | xmm r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      exact Operand.read_write_xmm_of_ne t hne v
    | mem a len => exact fun _ _ => rfl
    | _ => simp [Component.Agrees, Operand.write_xmm, fpuPtrOf]
  · have hz := zmm_map_xmmClear_write t.ZMM (xmmIndex r) v
    simp only [fixedPart, Operand.write_xmm, beforeFetch, resetStepFields]
    rw [hz]

/-- A step's bookkeeping, then an XMM write: only that register and RIP change. -/
theorem AgreesExcept.of_prepared_xmm {s t : RamState} (h : AgreesExcept [] s t) (r : BitVec 5)
    (v : BitVec 128) :
    AgreesExcept [.xmm r, .rip] s (finishStep ((Operand.xmm r : Operand 128).write t v)) :=
  (h.trans (AgreesExcept.write_xmm t r v)).trans (AgreesExcept.of_finishStep _)

/-- A step whose form ends in `writeResult` to XMM register `r` changes only `r` (its low 128
bits) and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writeResult_xmm (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    AgreesExcept [.xmm r, .rip] s
      (afterStep s length fun t => writeResult t (.xmm r) (v t) nextIP) :=
  AgreesExcept.of_prepared_xmm (AgreesExcept.prepare s (length + 1) nextIP) r _

/-- A load into XMM register `r` changes only `r` (its low 128 bits) and RIP (besides the per-step
bookkeeping). -/
theorem AgreesExcept.afterStep_load_xmm (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    AgreesExcept [.xmm r, .rip] s
      (afterStep s length fun t => writeResult (dataAccess t "load") (.xmm r) (v t) nextIP) := by
  have h0 : AgreesExcept [] s
      { dataAccess (afterFetches (beforeFetch s) (length + 1)) "load" with Next_IP := nextIP } := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  exact AgreesExcept.of_prepared_xmm h0 r _

/-- After a step whose form ends in `writeResult` to XMM register `r`, `r` reads the value
written. -/
theorem Operand.read_afterStep_writeResult_xmm (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    (Operand.xmm r : Operand 128).read
        (afterStep s length fun t => writeResult t (.xmm r) (v t) nextIP) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_xmm_self _ _ _

/-- After a load into XMM register `r`, `r` reads the value loaded. -/
theorem Operand.read_afterStep_load_xmm (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    (Operand.xmm r : Operand 128).read
        (afterStep s length fun t => writeResult (dataAccess t "load") (.xmm r) (v t) nextIP) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_xmm_self _ _ _

/-- Preservation for a form ending in `writeResult` to an XMM register: only that register,
`Next_IP`, RIP and per-step bookkeeping change. -/
theorem ReadyToStep.afterStep_writeResult_xmm [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeResult t (.xmm r) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeResult t (.xmm r) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- Preservation for a load into an XMM register: only that register, the oracle, the trace,
`Next_IP`, RIP and per-step bookkeeping change. -/
theorem ReadyToStep.afterStep_load_xmm [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (dataAccess t "load") (.xmm r) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult (dataAccess t "load") (.xmm r) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- SSE stays enabled across any effect (every effect's `AgreesExcept` keeps the control
registers). -/
theorem SsePre.sse_of_holds [Bindings] {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (hs : Prelude.SupportedSSE Bindings.processor s) : Prelude.SupportedSSE Bindings.processor s' :=
  SupportedSSE.of_agreesExcept h.agrees hs

/-- A CPUID feature (SSE2, …) stays reported across any effect (every effect's `AgreesExcept`
keeps the control registers and the CPUID configuration). -/
theorem SsePre.sse2_of_holds [Bindings] {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (hs : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true) :
    Prelude.ReportsCPUFeature Bindings.processor s' CPUID_SSE2_Encoding true :=
  reportsCPUFeature_of_sameControls (SameControls.of_fixedPart h.agrees.rest) hs

/-! ### Preconditions after a block

The `@[x86_pre]` carry-over lemmas of the SSE preconditions (`x86_mid`, `Program/Compose.lean`):
RIP from the effect, SSE and the CPUID reports kept by every effect, a memory operand's bytes
at its address in the canonical state. -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem SsePre.of_holds [Bindings] (h : e.Holds s s') {p : BitVec 64}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s) : SsePre p s' :=
  ⟨h.rip_of hrip, h.supportedSSE_iff.mpr hsse⟩

@[x86_pre] theorem Sse2Pre.of_holds [Bindings] (h : e.Holds s s') {p : BitVec 64}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true) :
    Sse2Pre p s' :=
  ⟨SsePre.of_holds h hrip hsse, h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem SseLoadNPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s) (ha : AddrObs addr)
    (hr : MemReadable s (addr (e.after s true)) len) : SseLoadNPre p addr len s' :=
  ⟨h.rip_of hrip, h.supportedSSE_iff.mpr hsse, MemReadable.carry h ho ha hr⟩

@[x86_pre] theorem Sse2LoadNPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (ha : AddrObs addr) (hr : MemReadable s (addr (e.after s true)) len) :
    Sse2LoadNPre p addr len s' :=
  ⟨SseLoadNPre.of_holds h ho hrip hsse ha hr, h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem SseLoadPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s) (ha : AddrObs addr)
    (hr : MemReadable s (addr (e.after s true)) 16) : SseLoadPre p addr s' :=
  ⟨h.rip_of hrip, h.supportedSSE_iff.mpr hsse, MemReadable.carry h ho ha hr⟩

@[x86_pre] theorem SseAlignedLoadPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s) (ha : AddrObs addr)
    (hr : MemReadable s (addr (e.after s true)) 16)
    (hal : (addr (e.after s true)).toNat % 16 = 0) : SseAlignedLoadPre p addr s' :=
  ⟨SseLoadPre.of_holds h ho hrip hsse ha hr, by rw [ha.eq ho]; exact hal⟩

@[x86_pre] theorem Sse2AlignedLoadPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (ha : AddrObs addr) (hr : MemReadable s (addr (e.after s true)) 16)
    (hal : (addr (e.after s true)).toNat % 16 = 0) : Sse2AlignedLoadPre p addr s' :=
  ⟨SseAlignedLoadPre.of_holds h ho hrip hsse ha hr hal, h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem SseStoreNPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ha : AddrObs addr)
    (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) : SseStoreNPre p codeLen addr len s' :=
  ⟨StorePre.of_holds h ho hrip ha hw hap, h.supportedSSE_iff.mpr hsse⟩

@[x86_pre] theorem Sse2StoreNPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (ha : AddrObs addr) (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    Sse2StoreNPre p codeLen addr len s' :=
  ⟨SseStoreNPre.of_holds h ho hrip hsse ha hw hap, h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem SseAlignedStorePre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} (hrip : e.rip = p)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (ha : AddrObs addr)
    (hw : MemWritable s (addr (e.after s true)) 16)
    (hap : RangeApart (addr (e.after s true)) 16 p codeLen)
    (hal : (addr (e.after s true)).toNat % 16 = 0) : SseAlignedStorePre p codeLen addr s' :=
  ⟨StorePre.of_holds h ho hrip ha hw hap, h.supportedSSE_iff.mpr hsse,
    by rw [ha.eq ho]; exact hal⟩

@[x86_pre] theorem Sse2AlignedStorePre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} (hrip : e.rip = p)
    (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (ha : AddrObs addr) (hw : MemWritable s (addr (e.after s true)) 16)
    (hap : RangeApart (addr (e.after s true)) 16 p codeLen)
    (hal : (addr (e.after s true)).toNat % 16 = 0) : Sse2AlignedStorePre p codeLen addr s' :=
  ⟨SseAlignedStorePre.of_holds h ho hrip hsse ha hw hap hal,
    h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem Sse2GprStorePre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (ha : AddrObs addr) (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    Sse2GprStorePre p codeLen addr len s' :=
  ⟨StorePre.of_holds h ho hrip ha hw hap, h.reportsCPUFeature_iff.mpr hsse2⟩

end Carry

end X86Proofs
