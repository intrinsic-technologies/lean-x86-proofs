import X86Proofs.Step.Paging
import X86Proofs.Core.Oracle
import X86Proofs.Core.Mode

/-!
# Logical to linear addresses

lean-x86's `Create_Logical_Address` and `Translate_Logical_To_Linear` for a flat 64-bit segment
(the null data segment of the code segment for a fetch, `flatData` for a data access), and the
checks the translation makes. Instruction fetch (`Step/Fetch.lean`), data accesses
(`Step/Memory.lean`) and the stack (`Program/ReadWrite/Stack.lean`) all use these lemmas.

- `createLogicalAddress_run`: the address record is drawn from the oracle
  (`logicalAddressFromOracle`, 464 bits).
- `isCanonicalWrtPagingMode_run`: an access of `count` bytes (any `count`, including the size-0
  check of `Check_New_RIP`) below 4 GiB is canonical, with or without LAM masking (`ignoreLAM`,
  which an instruction fetch sets).
- `isAlignmentCheckingEnabled_run`: alignment checking is off (CR0.AM clear).
- `AlignmentOk`: the alignment check of an alignment type passes.
- `translateLogicalToLinear_run`: in 64-bit mode, through a segment whose base is 0, the linear
  address is the offset; `translateLogicalToLinear_run_of_linear`: through any segment, the
  linear address `Compute_Linear_Address` gives (`base + offset` for FS or GS).
  `translateLogicalToLinear_run_of_selector` allows a loaded selector (SS itself). All three hold
  for a data access and for an instruction fetch (`fetch`, the flag `Mem_Fetch` passes as `true`).
- `isAligned_eq`: lean-x86's `Is_Aligned` test of a 64-bit address by a positive size (also used
  by a locked read, `Step/Memory.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The address record `Create_Logical_Address` builds for a one-byte access at `offset`, and the
oracle after the 464 bits it draws (the linear address, and a linear address, physical address
and translation record for each of the two pages). -/
noncomputable def logicalAddressFromOracle (o : X86.Runtime.Oracle) (segment : X86.Helpers.Segment)
    (cpl : Int) (offset : BitVec 64) : Address_Translation × X86.Runtime.Oracle :=
  let (linear, o) := o.take 64
  let (la1, o) := o.take 64
  let (pa1, o) := o.take 64
  let (tr1, o) := translationFromOracle o la1 pa1 .Memory_Type_Unknown
  let (la2, o) := o.take 64
  let (pa2, o) := o.take 64
  let (tr2, o) := translationFromOracle o la2 pa2 .Memory_Type_Unknown
  ({ num_bytes := 1, segment := segment, offset := offset, linear_address := linear,
     is_implicit_supervisor_mode_access := false, is_shadow_stack_access := false,
     translation_cpl := cpl, is_split_access := false, translation1 := tr1, translation2 := tr2 }, o)

theorem logicalAddressFromOracle_oracle (o : X86.Runtime.Oracle) (segment : X86.Helpers.Segment)
    (cpl : Int) (offset : BitVec 64) :
    (logicalAddressFromOracle o segment cpl offset).2 = oracleSkip o 464 := by
  simp [logicalAddressFromOracle, translationFromOracle, oracleTake_snd, oracleSkip_oracleSkip]

/-- `Create_Logical_Address` for an access of `n` bits: the record `logicalAddressFromOracle`
builds, with `n / 8` bytes; 464 oracle bits are drawn. -/
theorem createLogicalAddress_run (s : RamState) (segment : Segment) (offset : BitVec 64)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) :
    (Create_Logical_Address segment offset n).run s =
      (.ok { (logicalAddressFromOracle s.oracle segment s.CPL offset).1 with
          num_bytes := (n / 8 : Nat) },
        {s with oracle := oracleSkip s.oracle 464}) := by
  rw [← logicalAddressFromOracle_oracle s.oracle segment s.CPL offset]
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `createLogicalAddress_run` for the 80 bits (10 bytes) of an x87 extended-precision operand. -/
theorem createLogicalAddress_run80 (s : RamState) (segment : Segment) (offset : BitVec 64) :
    (Create_Logical_Address segment offset 80).run s =
      (.ok { (logicalAddressFromOracle s.oracle segment s.CPL offset).1 with num_bytes := 10 },
        {s with oracle := oracleSkip s.oracle 464}) := by
  rw [← logicalAddressFromOracle_oracle s.oracle segment s.CPL offset]
  rfl

/-- `CPUID_LAM` when the processor does not report LAM: `false`, the state unchanged (used by the
canonical-address check here and by `Direct_Memory_Offset`, `Step/Address.lean`). -/
theorem cpuidLAM_run [Bindings] (s : RamState)
    (hlam : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LAM_Encoding false) :
    (CPUID_LAM : X86.Runtime.SpecM X86.Exception RamState Bool) s = (.ok false, s) := by
  unfold CPUID_LAM
  exact readCPUIDFeature_run hlam

/-- An access of `count` bytes at `address` below 4 GiB is canonical (in 4-level paging, without
LAM). `count = 0` is `Check_New_RIP`'s check of the target alone. `ignoreLAM` is lean-x86's flag
for an instruction fetch, which is never LAM-masked; the processor reports no LAM, so the answer
is the same either way. -/
theorem isCanonicalWrtPagingMode_run [Bindings] (s : RamState) (address : BitVec 64) (count : Nat)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hcr4 : Prelude.SupportedIntegerCR4 s.CR4)
    (hlme : s.IA32_EFER.LME = 1)
    (hlam : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LAM_Encoding false)
    (haddr : address.toNat < 2^32) (hbound : address.toNat + count ≤ 2^32)
    (ignoreLAM : Bool := false) :
    (Is_Canonical_Wrt_Paging_Mode address ((count : Int) * 8) ignoreLAM).run s = (.ok true, s) := by
  have hfirst := isCanonicalWrtPosition48_run_of_low32 address haddr
  have hl := cpuidLAM_run s hlam
  have hnonneg : 0 ≤ ((count : Int) * 8) := by omega
  rcases Nat.eq_zero_or_pos count with rfl | hpos
  · simp [Is_Canonical_Wrt_Paging_Mode, hl, cr0PG_eq, cr4PAE_eq, X86.CR4.LA57, bind, pure, get,
      getThe, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, ExceptT.bindCont, StateT.bind,
      StateT.pure, MonadStateOf.get, StateT.get, Functor.map, StateT.map, Bind.bind, Pure.pure,
      ExceptT.lift, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, x86_runtime,
      supportedIntegerCR0_extractLsb_pg hcr0, supportedIntegerCR4_extractLsb_pae hcr4,
      supportedIntegerCR4_extractLsb_la57 hcr4, hlme, hfirst, Except.mapError, strictAnd, HAnd.hAnd,
      AndOp.and, Bool.and]
  have hlast : Is_Canonical_Wrt_Position
      (address + BitVec.ofNat 64 count - 1#64) 48 = .ok true := by
    apply isCanonicalWrtPosition48_run_of_low32
    have ha : (address + BitVec.ofNat 64 count).toNat = address.toNat + count := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := count) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]
    omega
  have hnonzero : ((count : Int) * 8) ≠ 0 := by omega
  simp [Is_Canonical_Wrt_Paging_Mode, hl, cr0PG_eq, cr4PAE_eq, X86.CR4.LA57, bind, pure, get,
    getThe, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    StateT.pure, MonadStateOf.get, StateT.get, Functor.map, StateT.map, Bind.bind, Pure.pure,
    ExceptT.lift, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, x86_runtime,
    (supportedIntegerCR0_extractLsb_pg hcr0), (supportedIntegerCR4_extractLsb_pae hcr4),
    (supportedIntegerCR4_extractLsb_la57 hcr4), hlme, stdSubtractInt_eq_ok (n := 64) _ _
        (by decide),
    hfirst, Except.mapError, strictAnd, HAnd.hAnd, AndOp.and, Bool.and, hnonneg, hnonzero]
  rw [hlast]
  rfl

/-- Alignment checking is off: CR0.AM is clear (`Prelude.CR0.AlignmentCheckingDisabled`). -/
theorem isAlignmentCheckingEnabled_run (s : RamState) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) :
    Is_Alignment_Checking_Enabled.run s = (.ok false, s) := by
  simp [Is_Alignment_Checking_Enabled, X86.CR0.AM, X86.RFLAGS.AC, get, getThe, liftM, bind,
    ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, MonadStateOf.get,
    monadLift, MonadLift.monadLift, pure, ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift,
    Functor.map, StateT.map, Bind.bind, x86_runtime, HAnd.hAnd, AndOp.and, strictAnd,
    (supportedIntegerCR0_extractLsb_am hcr0)]

/--
The alignment check of an access with alignment type `align` passes at `addr` for `len` bytes:
`Normal_Alignment` checks only if alignment checking is on (it is off, `CR0.AM = 0`),
`Explicitly_Unaligned` (MOVUPS) never checks, and `Explicitly_Aligned` (the other legacy SSE
`m128` operands, e.g. MOVAPS and XORPS) needs `addr` to be a multiple of `len`, else #GP.
-/
def AlignmentOk (align : Memory_Alignment_Type) (addr : BitVec 64) (len : Nat) : Prop :=
  align = .Explicitly_Aligned → addr.toNat % len = 0

theorem AlignmentOk.normal (addr : BitVec 64) (len : Nat) :
    AlignmentOk .Normal_Alignment addr len := fun h => nomatch h

theorem AlignmentOk.unaligned (addr : BitVec 64) (len : Nat) :
    AlignmentOk .Explicitly_Unaligned addr len := fun h => nomatch h

/-- The end of `Translate_Logical_To_Linear` in 64-bit mode, once the alignment check has passed:
the address is canonical and LASS is off. -/
local macro "linear_tail" hmode:term:max hcanonical:term:max hlass:term:max : tactic =>
  `(tactic| (
    rw [specM_bind_run _ _ $hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ $hcanonical]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ (checkLASSViolation_run _ _ $hlass)]
    rfl))

/--
Logical to linear in 64-bit mode through a segment whose linear address for the offset is `lin`
(`hcompute`; `lin` is the offset for the flat segments, `base + offset` for FS or GS reached by a
segment prefix): the linear address is `lin`, the access is not an implicit supervisor access, and
the checks pass (alignment of `lin` by `AlignmentOk`, canonicality of `lin` by `hcanonical`, LASS
off). `hnull` gives the null-selector test's answer `b`, which only matters with alignment checking
on. `fetch` is lean-x86's `is_instruction_fetch` (`true` from `Mem_Fetch`, else `false`), which
only reaches the canonicality check.
-/
theorem translateLogicalToLinear_run_of_linear [Bindings] (s : RamState)
    (logical : Address_Translation) (lin : BitVec 64)
    (hcompute : (Compute_Linear_Address logical.segment logical.offset userCodeSegment).run s =
      (.ok lin, s))
    (hsystem : Is_System_Segment logical.segment = .ok false)
    (hcode : logical.segment.is_code.isSome) (b : Bool)
    (hnull : Is_Null_Segment_Selector logical.segment.selector = .ok b)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hlma : s.IA32_EFER.LMA = 1)
    (hlass : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LASS_Encoding false)
    {fetch : Bool}
    (hcanonical : (Is_Canonical_Wrt_Paging_Mode lin (logical.num_bytes * 8) fetch).run s =
      (.ok true, s))
    (align : Memory_Alignment_Type) (hpos : 0 < logical.num_bytes)
    (halign : AlignmentOk align lin logical.num_bytes.toNat) :
    (Translate_Logical_To_Linear logical align userCodeSegment fetch).run s =
      (.ok { logical with
        linear_address := lin
        is_implicit_supervisor_mode_access := false }, s) := by
  have hmode := is64BitCodeSegment_userCodeSegment_run s hlma
  have hs : (liftM (Is_System_Segment logical.segment) :
      X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok false, s) := by
    rw [hsystem]; rfl
  unfold Translate_Logical_To_Linear
  rw [specM_bind_run _ _ hcompute]
  rw [specM_bind_run _ _ hs]
  cases align with
  | Normal_Alignment =>
    simp only [show (Memory_Alignment_Type.Normal_Alignment ==
        Memory_Alignment_Type.Explicitly_Aligned : Bool) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [specM_bind_run _ _ (isAlignmentCheckingEnabled_run s hcr0)]
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcode
    have hread : (X86.Runtime.readInitialized logical.segment.is_code :
        X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok c, s) := by
      rw [hc]; rfl
    rw [specM_bind_run _ _ hread, specM_bind_run _ _ hs, specM_bind_run _ _ hmode]
    have hnull' : (liftM (Is_Null_Segment_Selector logical.segment.selector) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok b, s) := by
      rw [hnull]; rfl
    rw [specM_bind_run _ _ hnull']
    simp only [HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr, OrOp.or, strictOr,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    linear_tail hmode hcanonical hlass
  | Explicitly_Aligned =>
    have hal : (liftM (Is_Aligned (n := 64) lin logical.num_bytes) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok true, s) := by
      have h := halign rfl
      have hz : (lin.toNat : Int) % logical.num_bytes = 0 := by
        have := congrArg (fun k : Nat => (k : Int)) h
        simp only [Int.natCast_emod, Int.toNat_of_nonneg (Int.le_of_lt hpos)] at this
        simpa using this
      simp [Is_Aligned, x86_runtime, Int.le_of_lt hpos, hpos, hz, liftM, monadLift,
        MonadLift.monadLift, ExceptT.run, Except.mapError, bind, pure, Except.bind, Except.pure]
      rfl
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [specM_bind_run _ _ hal]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    linear_tail hmode hcanonical hlass
  | Explicitly_Unaligned =>
    simp only [show (Memory_Alignment_Type.Explicitly_Unaligned ==
        Memory_Alignment_Type.Explicitly_Aligned : Bool) = false from rfl,
      show (Memory_Alignment_Type.Explicitly_Unaligned ==
        Memory_Alignment_Type.Normal_Alignment : Bool) = false from rfl,
      Bool.false_eq_true, ↓reduceIte]
    linear_tail hmode hcanonical hlass

/--
`translateLogicalToLinear_run` for a segment whose selector may be loaded (`hnull` gives the
null-selector test's answer `b`, which only matters with alignment checking on): the stack segment
SS as ENTER's writability check passes it (`checkLogicalAddressIsWritable_run`).
-/
theorem translateLogicalToLinear_run_of_selector [Bindings] (s : RamState)
    (logical : Address_Translation)
    (hcompute : (Compute_Linear_Address logical.segment logical.offset userCodeSegment).run s =
      (.ok logical.offset, s))
    (hsystem : Is_System_Segment logical.segment = .ok false)
    (hcode : logical.segment.is_code.isSome) (b : Bool)
    (hnull : Is_Null_Segment_Selector logical.segment.selector = .ok b)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hlma : s.IA32_EFER.LMA = 1)
    (hlass : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LASS_Encoding false)
    {fetch : Bool}
    (hcanonical : (Is_Canonical_Wrt_Paging_Mode logical.offset (logical.num_bytes * 8) fetch).run s =
      (.ok true, s))
    (align : Memory_Alignment_Type) (hpos : 0 < logical.num_bytes)
    (halign : AlignmentOk align logical.offset logical.num_bytes.toNat) :
    (Translate_Logical_To_Linear logical align userCodeSegment fetch).run s =
      (.ok { logical with
        linear_address := logical.offset
        is_implicit_supervisor_mode_access := false }, s) :=
  translateLogicalToLinear_run_of_linear s logical logical.offset hcompute hsystem hcode b hnull hcr0
    hlma hlass hcanonical align hpos halign

/--
Logical to linear in 64-bit mode, through a segment whose linear address is the offset
(`hcompute`; a null selector that is not a system segment, as `Mem_Fetch`'s and the flat data
segments are): the linear address is the offset, the access is not an implicit supervisor access,
and the checks pass (alignment by `AlignmentOk`, canonicality by `hcanonical`, LASS off).
-/
theorem translateLogicalToLinear_run [Bindings] (s : RamState) (logical : Address_Translation)
    (hcompute : (Compute_Linear_Address logical.segment logical.offset userCodeSegment).run s =
      (.ok logical.offset, s))
    (hsystem : Is_System_Segment logical.segment = .ok false)
    (hcode : logical.segment.is_code.isSome)
    (hnull : Is_Null_Segment_Selector logical.segment.selector = .ok true)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hlma : s.IA32_EFER.LMA = 1)
    (hlass : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LASS_Encoding false)
    {fetch : Bool}
    (hcanonical : (Is_Canonical_Wrt_Paging_Mode logical.offset (logical.num_bytes * 8) fetch).run s =
      (.ok true, s))
    (align : Memory_Alignment_Type) (hpos : 0 < logical.num_bytes)
    (halign : AlignmentOk align logical.offset logical.num_bytes.toNat) :
    (Translate_Logical_To_Linear logical align userCodeSegment fetch).run s =
      (.ok { logical with
        linear_address := logical.offset
        is_implicit_supervisor_mode_access := false }, s) :=
  translateLogicalToLinear_run_of_selector s logical hcompute hsystem hcode true hnull hcr0 hlma
    hlass hcanonical align hpos halign

/-- lean-x86's alignment test `Is_Aligned x k` of a 64-bit address by a positive size `k`: whether
`k` divides the address. -/
theorem isAligned_eq (x : BitVec 64) {k : Int} (hk : 0 < k) :
    Is_Aligned (n := 64) x k = .ok ((x.toNat : Int) % k == 0) := by
  simp [Is_Aligned, x86_runtime, Int.le_of_lt hk, hk, bind, pure, Except.bind, Except.pure]

end X86Proofs
