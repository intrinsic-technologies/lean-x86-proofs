import X86Proofs.Step.ReadyToStep
import X86Proofs.Core.Operand
import X86Proofs.Step.Debug

/-!
# Data reads and writes through the identity map

lean-x86's `Logical_Mem_Read` and `Logical_Mem_Write` for a flat 64-bit data segment, on a
machine with `Prelude`'s identity-mapped page tables: an access of 1, 2, 4 or 8 bytes at a linear
address below 4 GiB reaches exactly the bytes at the same physical address.

- `logicalMemRead_run`: a read returns `(Operand.mem addr).read s` and leaves the state as it
  was, except for the oracle bits of the address translation and the trace event `load`
  (`dataAccess`). The read may cross a 4 KiB page.
- `logicalMemWrite_run`: a write is `(Operand.mem addr).write s v`, plus the oracle bits and
  the trace event `store`. The page walk's dirty-bit update is a no-op on the identity map
  (`translate_run`), so nothing else changes; in particular the page tables are unchanged
  unless the written bytes overlap them (`IdentityPageTableMemory.memStore`). A non-temporal
  write (the last argument `nt`, lean-x86's `non_temporal_hint`: MOVNTI, MOVNTPS, …) is the same
  write: the hint only changes the memory type the physical write is given, which it ignores.
  The write may cross a 4 KiB page.

The bytes must be present in RAM (lean-x86 fails on a missing byte). A page-crossing access is
translated once per page (`Translate_Linear_To_Physical`'s split branch), then read or written
in one physical access whose byte `i` goes to the first or second translation. On the identity
map both translations are identity and leave the state unchanged, so byte `i` is still at
`addr + i` (`physicalByteAddress_dataPhysical`), and the bookkeeping is the same as for a one-page access:
the 464 oracle bits are drawn once, by `Create_Logical_Address`, and there is one trace event.
Reads and writes both go through `dataPhysical`, which covers the two cases. Both translations
are made before any byte is written, so a fault on the second page would come before the first
byte changes (on the identity map below 4 GiB neither faults).

Through a segment-override prefix (FS or GS) the access goes through that segment, whose base is
added to the offset (`segBase`, `SegReady`): `logicalMemRead_run_seg` and `logicalMemWrite_run_seg`
take any segment whose linear address for the offset is known (`SegAccess`), and read or write the
operand at that linear address. `ctxSegment ctx` and `segAddr ctx` are the segment and linear
address after a decode context (`SegAccess.ctx`); `getEffectiveSegment_run_of_seg`: lean-x86's
effective segment after such a prefix (the string instructions' DS:RSI operand).

A locked access (a LOCK form's `acquire_lock` read and `release_lock` write) is the unlocked one
when it lies in one cache line and the bus-lock-detect CPUID query is answered (`LockReady`):
`logicalMemRead_run_seg_lock`, `logicalMemWrite_run_seg_lock`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers
open X86.Machine.Bindings.PhysicalAccess

/-- The machine facts a data access needs: the fetch facts plus the CPL range lean-x86 asserts
on a physical access, and data breakpoints disabled. -/
structure DataReady [Bindings] (s : RamState) : Prop extends FetchReady s where
  cpl : 0 ≤ s.CPL ∧ s.CPL ≤ 3
  debug : Prelude.DR7.BreakpointsDisabled s.DR7

/--
The state after a data access, apart from what the access reads or writes: the address
translation uses up 464 oracle bits, and the physical access appends `event` (`load` or `store`)
to lean-x86's trace of memory accesses.
-/
def dataAccess (s : RamState) (event : String) : RamState :=
  { s with oracle := oracleSkip s.oracle 464,
           traceEventsRev := ("isa.memory", event) :: s.traceEventsRev }

@[simp] theorem Operand.read_reg_dataAccess {n : Nat} (s : RamState) (event : String)
    (r : BitVec 5) :
    (Operand.reg r : Operand n).read (dataAccess s event) = (Operand.reg r : Operand n).read s :=
  rfl

theorem nullSegment_run (segment : Segment) : Null_Segment segment = .ok (nullDataSegment segment) :=
  rfl

theorem getEffectiveSegment_run (context : Instruction_Context) (segment : Segment)
    (hseg : context.seg_prefix_present = false) (hmode : context.is_mode64 = true) :
    Get_Effective_Segment context segment = .ok (nullDataSegment segment) := by
  simp [Get_Effective_Segment, hseg, hmode]
  rfl

/-! ### Logical to linear -/

theorem flatData_system (isStack : Bool) : Is_System_Segment (flatData isStack) = .ok false := by
  cases isStack <;> rfl

/-- Logical to linear for a flat data access: the linear address is the offset
(`translateLogicalToLinear_run` for `flatData`). -/
theorem translateLogicalToLinear_run_of_flatData [Bindings] (s : RamState) (logical : Address_Translation)
    (isStack : Bool) (hsegment : logical.segment = flatData isStack)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hlma : s.IA32_EFER.LMA = 1)
    (hlass : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LASS_Encoding false)
    (hcanonical : (Is_Canonical_Wrt_Paging_Mode logical.offset (logical.num_bytes * 8) false).run s =
      (.ok true, s))
    (align : Memory_Alignment_Type) (hpos : 0 < logical.num_bytes)
    (halign : AlignmentOk align logical.offset logical.num_bytes.toNat) :
    (Translate_Logical_To_Linear logical align userCodeSegment).run s =
      (.ok { logical with
        linear_address := logical.offset
        is_implicit_supervisor_mode_access := false }, s) :=
  translateLogicalToLinear_run s logical
    (by rw [hsegment]; exact flatData_linear_address s logical.offset isStack hlma)
    (by rw [hsegment, flatData_system]) (by rw [hsegment]; cases isStack <;> rfl)
    (by rw [hsegment]; cases isStack <;> rfl) hcr0 hlma hlass hcanonical align hpos halign

/-! ### Segments with a base (FS and GS) -/

/-- The base of segment `seg`, as lean-x86's `Get_Segment_Base` reads it from the descriptor's
base fields (0 if a base bit is uninitialized; `SegReady` rules that out). FS and GS are the
segments with a nonzero base in 64-bit mode. -/
noncomputable def segBase (seg : Segment) : BitVec 64 :=
  match Get_Segment_Base seg with
  | .ok b => b
  | .error _ => 0

/-- A segment a segment-override prefix (FS or GS) can use for a 64-bit data access: its base
reads (`segBase`), it is a 64-bit-mode segment (so `Compute_Linear_Address` adds the base), not a
system segment, and its code flag is initialized (the alignment check reads it). -/
structure SegReady (seg : Segment) : Prop where
  base : Get_Segment_Base seg = .ok (segBase seg)
  mode64 : seg.is_64bit_mode_data_segment = some true
  system : Is_System_Segment seg = .ok false
  code : seg.is_code.isSome

/-- What a data access through segment `seg` at offset `off` needs of the segment: in 64-bit mode
its linear address is `lin`, it is not a system segment, its code flag and selector can be read.
`SegAccess.flat`: a flat data segment, `lin = off`; `SegReady.access`: FS or GS,
`lin = segBase seg + off`. -/
structure SegAccess (seg : Segment) (off lin : BitVec 64) : Prop where
  linear : ∀ s : RamState, s.IA32_EFER.LMA = 1 →
    (Compute_Linear_Address seg off userCodeSegment).run s = (.ok lin, s)
  system : Is_System_Segment seg = .ok false
  code : seg.is_code.isSome
  null : ∃ b, Is_Null_Segment_Selector seg.selector = .ok b

theorem isNullSegmentSelector_ok (sel : Segment_Selector) :
    ∃ b, Is_Null_Segment_Selector sel = .ok b :=
  ⟨_, rfl⟩

theorem SegAccess.flat (isStack : Bool) (off : BitVec 64) :
    SegAccess (flatData isStack) off off :=
  ⟨fun s h => flatData_linear_address s off isStack h, flatData_system isStack,
    by cases isStack <;> rfl, isNullSegmentSelector_ok _⟩

/-- The user profile's stack segment (SS) is flat: an offset is its own linear address (ENTER reads
the enclosing frames' pointers through SS itself). -/
theorem SegAccess.userStack (off : BitVec 64) : SegAccess userStackSegment off off :=
  ⟨fun s h => computeLinearAddress_userStackSegment_run s off h, rfl, rfl,
    isNullSegmentSelector_ok _⟩

theorem SegReady.access {seg : Segment} (h : SegReady seg) (off : BitVec 64) :
    SegAccess seg off (segBase seg + off) :=
  ⟨fun s hl => computeLinearAddress_of_base s seg off _ hl h.mode64 false h.system h.base,
    h.system, h.code, isNullSegmentSelector_ok _⟩

/-- The segment a data access goes through after the decode context `ctx`, for an operand whose
default segment is SS (`isStack`) or DS: the override segment if `ctx` has a segment prefix (FS or
GS), else the flat data segment. -/
noncomputable def ctxSegment (ctx : Instruction_Context) (isStack : Bool) : Segment :=
  if ctx.seg_prefix_present then ctx.segment else flatData isStack

/-- The linear address of offset `a` after the decode context `ctx`: `a` plus the override
segment's base if `ctx` has a segment prefix (FS or GS), else `a` (the flat segments have base 0).
On a context without a segment prefix it reduces to `a` by `rfl`. -/
noncomputable def segAddr (ctx : Instruction_Context) (a : BitVec 64) : BitVec 64 :=
  if ctx.seg_prefix_present then segBase ctx.segment + a else a

theorem segAddr_of_not {ctx : Instruction_Context} (h : ctx.seg_prefix_present = false)
    (a : BitVec 64) : segAddr ctx a = a := by
  simp [segAddr, h]

theorem segAddr_of_seg {ctx : Instruction_Context} (h : ctx.seg_prefix_present = true)
    (a : BitVec 64) : segAddr ctx a = segBase ctx.segment + a := by
  simp [segAddr, h]

/-- The linear address of `off + d` after `ctx` is that of `off`, plus `d`. -/
theorem segAddr_add (ctx : Instruction_Context) (off d : BitVec 64) :
    segAddr ctx (off + d) = segAddr ctx off + d := by
  unfold segAddr
  split
  · rw [BitVec.add_assoc]
  · rfl

/-- The access through `ctxSegment` is at `segAddr`, given the override segment is ready. -/
theorem SegAccess.ctx {ctx : Instruction_Context}
    (h : ctx.seg_prefix_present = true → SegReady ctx.segment) (isStack : Bool) (off : BitVec 64) :
    SegAccess (ctxSegment ctx isStack) off (segAddr ctx off) := by
  unfold ctxSegment segAddr
  cases hs : ctx.seg_prefix_present
  · exact SegAccess.flat isStack off
  · exact (h hs).access off

/-- `SegAccess.ctx` at `off + d`: the access at `segAddr ctx off + d` (the second part of an
access split in two, as for the 80-bit x87 operands). -/
theorem SegAccess.ctx_add {ctx : Instruction_Context}
    (h : ctx.seg_prefix_present = true → SegReady ctx.segment) (isStack : Bool)
    (off d : BitVec 64) :
    SegAccess (ctxSegment ctx isStack) (off + d) (segAddr ctx off + d) :=
  segAddr_add ctx off d ▸ SegAccess.ctx h isStack (off + d)

/-- The segment `Get_Effective_Segment` picks in 64-bit mode for default segment `seg`: the
prefix's segment (FS or GS) if `ctx` has a segment prefix, else `seg`'s null data segment. -/
noncomputable def effSegment (ctx : Instruction_Context) (seg : Segment) : Segment :=
  if ctx.seg_prefix_present then ctx.segment else nullDataSegment seg

theorem effSegment_idem (ctx : Instruction_Context) (seg : Segment) :
    effSegment ctx (effSegment ctx seg) = effSegment ctx seg := by
  unfold effSegment
  cases ctx.seg_prefix_present <;> rfl

theorem effSegment_of_not {ctx : Instruction_Context} (h : ctx.seg_prefix_present = false)
    (seg : Segment) : effSegment ctx seg = nullDataSegment seg := by
  simp [effSegment, h]

/-- With a segment-override prefix (FS or GS in 64-bit mode) the effective segment is the
prefix's, whatever the default segment. -/
theorem getEffectiveSegment_run_of_seg (context : Instruction_Context) (segment : Segment)
    (hseg : context.seg_prefix_present = true) :
    Get_Effective_Segment context segment = .ok context.segment := by
  simp [Get_Effective_Segment, hseg]
  rfl

theorem getEffectiveSegment_run_eff (context : Instruction_Context) (segment : Segment)
    (hmode : context.is_mode64 = true) :
    Get_Effective_Segment context segment = .ok (effSegment context segment) := by
  unfold effSegment
  cases h : context.seg_prefix_present
  · simp [Get_Effective_Segment, h, hmode]
    rfl
  · simp [Get_Effective_Segment, h]
    rfl

/-! ### Checks that pass in 64-bit mode with breakpoints off -/

theorem checkReadPermission_run (s : RamState) (segment : Segment) (hcs : s.CS = userCodeSegment)
    (hlma : s.IA32_EFER.LMA = 1) : (Check_Read_Permission segment).run s = (.ok (), s) := by
  unfold Check_Read_Permission
  rw [specM_bind_run _ _ (in64BitMode_of_userCodeSegment hcs hlma)]
  rfl

theorem checkWritePermission_run (s : RamState) (segment : Segment) (hcs : s.CS = userCodeSegment)
    (hlma : s.IA32_EFER.LMA = 1) : (Check_Write_Permission segment).run s = (.ok (), s) := by
  unfold Check_Write_Permission
  rw [specM_bind_run _ _ (in64BitMode_of_userCodeSegment hcs hlma)]
  rfl

/-! ### Physical accesses -/

theorem traceEvent_run {exception : Type} (s : RamState) (channel message : String) :
    (X86.Runtime.traceEvent (exception := exception) channel message).run s =
      (.ok (), { s with traceEventsRev := (channel, message) :: s.traceEventsRev }) := rfl

theorem writePhysicalByte_run [instBindings : Bindings] {exception : Type} (s : RamState)
    (hsmrr : Prelude.SMRRUnblocked instBindings s) (address : BitVec 64) (byte : UInt8)
    (h : (s.external[address]?).isSome) :
    (writePhysicalByte (σ := Ram) (exception := exception) address byte).run s =
      (.ok (), { s with external := s.external.insert address byte }) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  unfold writePhysicalByte
  simp only [smrrBlocked_run s hsmrr, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind,
    get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    Functor.map, StateT.map, StateT.get, pure, ExceptT.bindCont, StateT.pure, Except.mapError,
    Bool.false_eq_true, ↓reduceIte, PhysicalMemory.read, hb, Option.isNone_some, set,
    StateT.set, PhysicalMemory.write]

/-- Inserting bytes one state at a time is inserting them into memory. -/
theorem foldl_insert_external (items : List Nat) (address : Nat → BitVec 64)
    (byte : Nat → UInt8) (s : RamState) :
    items.foldl (fun t i => { t with external := t.external.insert (address i) (byte i) }) s =
      { s with external := items.foldl (fun m i => m.insert (address i) (byte i)) s.external } := by
  induction items generalizing s with
  | nil => rfl
  | cons i items ih => exact ih _

theorem writeBytes_run [instBindings : Bindings] {exception : Type} (n : Nat) (hn : n % 8 = 0)
    (address : Nat → BitVec 64) (value : BitVec (n : Int).toNat) (s : RamState)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (h : ∀ i, i < n / 8 → (s.external[address i]?).isSome) :
    (writeBytes (σ := Ram) (exception := exception) (n : Int) address value).run s =
      (.ok (), { s with external := (List.range (n / 8)).foldl (fun m i =>
        m.insert (address i) (UInt8.ofNat (value.toNat >>> (8 * i)))) s.external }) := by
  unfold writeBytes
  rw [specM_bind_run _ _ (byteCount_run_nat n hn s)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  have hloop := specM_forIn_foldl_run (exception := exception) (List.range (n / 8))
    (fun i (_ : PUnit) => do
      writePhysicalByte (σ := Ram) (exception := exception) (address i)
        (UInt8.ofNat (value.toNat >>> (8 * i)))
      pure (.yield ()))
    (fun i t => { t with
      external := t.external.insert (address i) (UInt8.ofNat (value.toNat >>> (8 * i))) })
    (fun t => Prelude.SMRRUnblocked instBindings t ∧
      ∀ i, i < n / 8 → (t.external[address i]?).isSome) s ⟨hsmrr, h⟩
    (by
      intro i hi t ht
      rw [specM_bind_run _ _ (writePhysicalByte_run t ht.1 (address i) _
        (ht.2 i (by simpa using hi)))]
      rfl)
    (by
      intro i hi t ht
      refine ⟨ht.1, fun j hj => ?_⟩
      simp only [Std.ExtHashMap.getElem?_insert]
      split
      · rfl
      · exact ht.2 j hj)
  rw [specM_bind_run _ _ hloop, foldl_insert_external]
  rfl

/-- What the identity map translates a single-page access to (`translateLinearToPhysical_run`). -/
noncomputable def identityPhysical (linear : Address_Translation) : Address_Translation :=
  singleTranslation linear (writeBackIdentityTranslation linear)

/-- What the identity map translates a page-crossing access to (`translateLinearToPhysical_run_of_split`). -/
noncomputable def identitySplitPhysical (linear : Address_Translation) : Address_Translation :=
  splitTranslation linear (writeBackIdentityTranslation (firstPageAccess linear))
    (writeBackIdentityTranslation (secondPageAccess linear))

/--
What the identity map translates a data access to, whether or not it crosses a 4 KiB page: one
translation (`identityPhysical`) or one per page (`identitySplitPhysical`). Either way byte `i`
is at physical address `linear_address + i` (`physicalByteAddress_dataPhysical`).
-/
noncomputable def dataPhysical (linear : Address_Translation) : Address_Translation :=
  if 4096 < (linear.linear_address.toNat : Int) % 4096 + linear.num_bytes then
    identitySplitPhysical linear
  else identityPhysical linear

theorem pageHeadBytes_eq (address : BitVec 64) :
    pageHeadBytes address = ((4096 - address.toNat % 4096 : Nat) : Int) := by
  unfold pageHeadBytes
  omega

theorem checkTranslation_dataPhysical_run {exception : Type} (linear : Address_Translation) (n : Nat)
    (hn : n % 8 = 0) (hnum : linear.num_bytes = (n / 8 : Nat)) (s : RamState) :
    (checkTranslation (σ := Ram) (exception := exception) (dataPhysical linear) n).run s =
      (.ok (), s) := by
  unfold checkTranslation dataPhysical
  rw [specM_bind_run _ _ (byteCount_run_nat n hn s)]
  split
  · rename_i hcross
    have hfirst : ¬(pageHeadBytes linear.linear_address ≤ 0 ∨
        pageHeadBytes linear.linear_address ≥ ((n / 8 : Nat) : Int)) := by
      rw [pageHeadBytes_eq]
      omega
    simp only [identitySplitPhysical, splitTranslation, writeBackIdentityTranslation,
      identityTranslation, firstPageAccess, Bool.true_and, Int.ofNat_eq_natCast]
    split
    · rename_i h
      exact absurd ((Bool.or_eq_true _ _).mp h |>.imp of_decide_eq_true of_decide_eq_true) hfirst
    · rfl
  · rfl

/-- The identity map's translation, single or split, puts byte `i` at `linear_address + i`. -/
theorem physicalByteAddress_dataPhysical (linear : Address_Translation) (addr : BitVec 64)
    (hla : linear.linear_address = addr) (i : Nat) :
    physicalByteAddress (dataPhysical linear) i = addr + BitVec.ofNat 64 i := by
  unfold dataPhysical
  split
  · simp only [physicalByteAddress, identitySplitPhysical, splitTranslation,
      writeBackIdentityTranslation, identityTranslation, firstPageAccess, secondPageAccess,
      Bool.true_and, pageHeadBytes_eq, BitVec.ofInt_natCast, Int.toNat_natCast, hla]
    split
    · rename_i hi
      have hi : 4096 - addr.toNat % 4096 ≤ i := by simpa using hi
      change addr + BitVec.ofNat 64 (4096 - addr.toNat % 4096) +
        BitVec.ofNat 64 (i - (4096 - addr.toNat % 4096)) = _
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' hi]
    · rfl
  · simp only [physicalByteAddress, identityPhysical, singleTranslation, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, writeBackIdentityTranslation, identityTranslation, hla]
    rfl

@[simp] theorem dataPhysical_cpl (linear : Address_Translation) :
    (dataPhysical linear).translation_cpl = linear.translation_cpl := by
  unfold dataPhysical
  split <;> rfl

/-- The first translation of a data access on the identity map: physical address = linear
address, write-back. -/
theorem dataPhysical_translation1 (linear : Address_Translation) :
    (dataPhysical linear).translation1.physical_address = linear.linear_address ∧
      (dataPhysical linear).translation1.memory_type = .Memory_Type_Write_Back := by
  unfold dataPhysical
  split <;> exact ⟨rfl, rfl⟩

theorem memLoad_eq_assembleBytes (m : Ram) (addr : BitVec 64) (n : Nat) :
    memLoad m addr n = assembleBytes n (n / 8) fun i => memByte m (addr + BitVec.ofNat 64 i) :=
  rfl

theorem physicalMemRead_dataPhysical_run [instBindings : Bindings] (linear : Address_Translation)
    (addr : BitVec 64) (hla : linear.linear_address = addr)
    (n : Nat) (hn : n % 8 = 0) (hnum : linear.num_bytes = (n / 8 : Nat)) (s : RamState)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hcpl : 0 ≤ linear.translation_cpl ∧ linear.translation_cpl ≤ 3)
    (h : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Physical_Mem_Read (σ := Ram) (dataPhysical linear) n).run s =
      (.ok (memLoad s.external addr n),
        { s with traceEventsRev := ("isa.memory", "load") :: s.traceEventsRev }) := by
  have hc : X86.Runtime.inRange (dataPhysical linear).translation_cpl 0 3 = true := by
    simp only [dataPhysical_cpl, x86_runtime, hcpl.1, decide_true, hcpl.2, Bool.and_self]
  have hread := readBytes_run_nat (exception := Empty) n hn
    (physicalByteAddress (dataPhysical linear))
    (fun i => memByte s.external (addr + BitVec.ofNat 64 i)) s hsmrr
    (fun i hi => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h i hi)
      rw [physicalByteAddress_dataPhysical linear addr hla]
      simp [memByte, PhysicalMemory.read, hb])
  unfold Physical_Mem_Read
  simp only [x86_runtime, pure_bind, hc]
  apply specM_liftNoSourceException_run
  change (do
    checkTranslation (dataPhysical linear) n
    let value ← readBytes n (physicalByteAddress (dataPhysical linear))
    X86.Runtime.traceEvent "isa.memory" "load"
    pure value).run s = _
  rw [specM_bind_run _ _ (checkTranslation_dataPhysical_run linear n hn hnum s), specM_bind_run _ _ hread,
    specM_bind_run _ _ (traceEvent_run s _ _)]
  rfl

/-- The physical write of `n` bits after the identity map's translation, single or split
(`dataPhysical`): byte `i` of the value goes to `addr + i`. -/
theorem physicalMemWrite_dataPhysical_run [instBindings : Bindings] (linear : Address_Translation)
    (addr : BitVec 64) (hla : linear.linear_address = addr)
    (n : Nat) (hn : n % 8 = 0) (hnum : linear.num_bytes = (n / 8 : Nat)) (value : BitVec n)
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hcpl : 0 ≤ linear.translation_cpl ∧ linear.translation_cpl ≤ 3)
    (h : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Physical_Mem_Write (σ := Ram) (dataPhysical linear) n value).run s =
      (.ok (), { s with
        external := memStore s.external addr value
        traceEventsRev := ("isa.memory", "store") :: s.traceEventsRev }) := by
  have hc : X86.Runtime.inRange (dataPhysical linear).translation_cpl 0 3 = true := by
    simp only [dataPhysical_cpl, x86_runtime, hcpl.1, decide_true, hcpl.2, Bool.and_self]
  have hwrite := writeBytes_run (exception := Empty) n hn
    (physicalByteAddress (dataPhysical linear)) value s hsmrr (fun i hi => by
      rw [physicalByteAddress_dataPhysical linear addr hla]
      exact h i hi)
  unfold Physical_Mem_Write
  simp only [x86_runtime, pure_bind, hc]
  apply specM_liftNoSourceException_run
  change (do
    checkTranslation (dataPhysical linear) n
    writeBytes n (physicalByteAddress (dataPhysical linear)) value
    X86.Runtime.traceEvent "isa.memory" "store").run s = _
  rw [specM_bind_run _ _ (checkTranslation_dataPhysical_run linear n hn hnum s),
    specM_bind_run _ _ hwrite, traceEvent_run]
  simp only [memStore, PhysicalMemory.write, physicalByteAddress_dataPhysical linear addr hla]

/-! ### Logical accesses -/

/-- `DataReady` depends only on the control registers (`SameControls`), CS, CR3, EFER, the CPL,
DR7 and the page-table bytes. -/
theorem DataReady.of_sameControls [Bindings] {s t : RamState} (h : DataReady s) (hst : SameControls s t)
    (hcs : t.CS = s.CS) (hcr3 : t.CR3 = s.CR3) (hefer : t.IA32_EFER = s.IA32_EFER)
    (hcpl : t.CPL = s.CPL) (hdr7 : t.DR7 = s.DR7) (htables : IdentityPageTableMemory t.external) :
    DataReady t :=
  { cs := hcs.trans h.cs, cr0 := hst.cr0 ▸ h.cr0, cr3 := hcr3.trans h.cr3, cr4 := hst.cr4 ▸ h.cr4,
    efer := hefer ▸ h.efer, maxPhysical := h.maxPhysical, early := h.early,
    lam := reportsCPUFeature_of_sameControls hst h.lam, lass := reportsCPUFeature_of_sameControls hst h.lass,
    cetSS := h.cetSS.imp fun _ => reportsCPUFeature_of_sameControls hst,
    smrr := smrrUnblocked_of_sameControls hst h.smrr,
    memoryType := writeBackMemoryType_of_sameControls hst h.memoryType, tables := htables,
    cpl := hcpl ▸ h.cpl, debug := hdr7 ▸ h.debug }

theorem DataReady.oracle [Bindings] {s : RamState} (h : DataReady s) (o : X86.Runtime.Oracle) :
    DataReady { s with oracle := o } :=
  h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables

theorem DataReady.dataAccess [Bindings] {s : RamState} (h : DataReady s) (event : String) :
    DataReady (dataAccess s event) :=
  h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables

/-- `DataReady` survives setting `Next_IP`. -/
theorem DataReady.withNextIP [Bindings] {s : RamState} (h : DataReady s) (n : BitVec 64) :
    DataReady (withNextIP s n) :=
  h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables

/-- The linear address a flat data access of `n` bits at `addr` translates through. -/
noncomputable def dataLinear (s : RamState) (isStack : Bool) (addr : BitVec 64) (n : Nat) :
    Address_Translation :=
  { (logicalAddressFromOracle s.oracle (flatData isStack) s.CPL addr).1 with
    num_bytes := (n / 8 : Nat)
    linear_address := addr
    is_implicit_supervisor_mode_access := false }

/--
The address translation of a data access of `count` bytes below 4 GiB, for any access type: the
identity map's (`dataPhysical`), and the state is unchanged. An access within one page translates
once (`translateLinearToPhysical_run`), a page-crossing one once per page
(`translateLinearToPhysical_run_of_split`).
-/
theorem translateLinearToPhysical_run_of_dataReady [instBindings : Bindings] (s : RamState) (h : DataReady s)
    (linear : Address_Translation) (access : Memory_Access_Type) (count : Nat)
    (hnum : linear.num_bytes = count) (hpos : 0 < count)
    (hshadow : linear.is_shadow_stack_access = false)
    (hlow : linear.linear_address.toNat + count ≤ 2^32) :
    (Translate_Linear_To_Physical linear access).run s = (.ok (dataPhysical linear), s) := by
  have ht (a : Address_Translation) (hsh : a.is_shadow_stack_access = false)
      (ha : a.linear_address.toNat < 2^32) :
      (Translate a access).run s = (.ok (writeBackIdentityTranslation a), s) :=
    translate_run s h.smrr h.memoryType h.cr3 h.cr4 h.efer.lme h.maxPhysical h.efer.nxe
      h.early h.tables h.cetSS a access hsh ha
  unfold dataPhysical
  split
  · rename_i hcross
    have hsecond : (secondPageAccess linear).linear_address.toNat < 2^32 := by
      change (linear.linear_address.toNat + (BitVec.ofInt 64
        (pageHeadBytes linear.linear_address)).toNat) % 2^64 < 2^32
      rw [pageHeadBytes_eq, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      rw [hnum] at hcross
      omega
    exact translateLinearToPhysical_run_of_split s s s linear access _ _ h.cr0
      (isLinearAccessSplitAcross4KBPages_run_of_crosses s _ _ h.cr0 (by omega) hcross) (ht _ hshadow (by simp [firstPageAccess]; omega))
      (ht _ hshadow hsecond)
  · exact translateLinearToPhysical_run s s linear access _ h.cr0
      (isLinearAccessSplitAcross4KBPages_run_of_fits s _ _ h.cr0 (by omega) (by omega)) (ht linear hshadow (by omega))

/-- The linear address record of a data access of `n` bits at offset `off` through `seg`, whose
linear address is `lin`. -/
noncomputable def accessLinear (s : RamState) (seg : Segment) (off lin : BitVec 64) (n : Nat) :
    Address_Translation :=
  { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
    num_bytes := (n / 8 : Nat)
    linear_address := lin
    is_implicit_supervisor_mode_access := false }

/--
A data read of `n` bits (`n` ∈ {8, 16, 32, 64, 128}) at offset `off` through a segment whose linear
address for it is `lin` (`SegAccess`: `lin = off` for a flat segment, `base + off` for FS or GS),
below 4 GiB, with the bytes present in RAM and the alignment check of `align` passing
(`AlignmentOk`): returns the memory operand at `lin` and changes nothing but the bookkeeping
(`dataAccess s "load"`). The read may cross a 4 KiB page.
-/
theorem logicalMemRead_run_seg_align [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128)
    (access : Memory_Access_Type)
    (haccess : access = .Memory_Read ∨ access = .Memory_Read_Modify_Write)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align lin (n / 8))
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Read seg off n access align false).run s =
      (.ok ((Operand.mem lin : Operand n).read s), dataAccess s "load") := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t lin (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
      num_bytes := (n / 8 : Nat) } lin (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull
    ht.cr0 ht.efer.lma ht.lass hcan align
    (by simp only; omega)
    (by
      show AlignmentOk align lin ((n / 8 : Nat) : Int).toNat
      rw [Int.toNat_natCast]; exact halign)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin n)
    access (n / 8) rfl hcount rfl hlow
  have hphys := physicalMemRead_dataPhysical_run (accessLinear s seg off lin n) lin rfl n
    (by omega) rfl t ht.smrr ht.cpl hmem
  unfold Logical_Mem_Read
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> rcases haccess with rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
    rw [specM_bind_run _ _ (checkReadPermission_run _ _ h.cs h.efer.lma)]
    try rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma)]
    rw [specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by decide)),
      specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
        (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
    refine (specM_bind_run _ _ hlin).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (checkDataReadBreakpoint_run _ _ _ ht.debug)).trans ?_
    refine (specM_bind_run _ _ htr).trans ?_
    exact hphys

/--
A data read of `n` bits (`n` ∈ {8, 16, 32, 64, 128}) at `addr` through a flat data segment, below
4 GiB, with the bytes present in RAM and the alignment check of `align` passing (`AlignmentOk`):
returns the memory operand's value and changes nothing but the bookkeeping
(`dataAccess s "load"`). The read may cross a 4 KiB page: lean-x86 then translates each page
separately, but still reads once, so the bookkeeping is the same.
-/
theorem logicalMemRead_run_align [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128)
    (access : Memory_Access_Type)
    (haccess : access = .Memory_Read ∨ access = .Memory_Read_Modify_Write)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align addr (n / 8))
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Read (flatData isStack) addr n access align false).run s =
      (.ok ((Operand.mem addr : Operand n).read s), dataAccess s "load") :=
  logicalMemRead_run_seg_align s h _ addr addr (SegAccess.flat isStack addr) n hn access haccess
    align halign hlow hmem

/--
`logicalMemRead_run_seg_align` for the normal alignment type of the integer instructions, at
`n` ∈ {8, 16, 32, 64}.
-/
theorem logicalMemRead_run_seg [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (access : Memory_Access_Type)
    (haccess : access = .Memory_Read ∨ access = .Memory_Read_Modify_Write)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Read seg off n access .Normal_Alignment false).run s =
      (.ok ((Operand.mem lin : Operand n).read s), dataAccess s "load") :=
  logicalMemRead_run_seg_align s h seg off lin hseg n (by omega) access haccess _
    (AlignmentOk.normal _ _) hlow hmem

/--
`logicalMemRead_run_align` for the normal alignment type of the integer instructions, at
`n` ∈ {8, 16, 32, 64}.
-/
theorem logicalMemRead_run [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (access : Memory_Access_Type)
    (haccess : access = .Memory_Read ∨ access = .Memory_Read_Modify_Write)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Read (flatData isStack) addr n access .Normal_Alignment false).run s =
      (.ok ((Operand.mem addr : Operand n).read s), dataAccess s "load") :=
  logicalMemRead_run_align s h isStack addr n (by omega) access haccess _
    (AlignmentOk.normal _ _) hlow hmem

/--
A data write of `n` bits (`n` ∈ {8, 16, 32, 64, 128}) at offset `off` through a segment whose linear
address for it is `lin` (`SegAccess`), below 4 GiB (it may cross a 4 KiB page), with the bytes
present in RAM and the alignment check of `align` passing (`AlignmentOk`): it is the memory
operand's write at `lin`, plus the bookkeeping (`dataAccess s "store"`). The same with the
non-temporal hint `nt` set (MOVNTI, MOVNTPS, …): the hint turns the write-back memory type of the
identity map into write-combining, which the physical write does not look at.
-/
theorem logicalMemWrite_run_seg_align [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align lin (n / 8))
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) seg off v align false false .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem lin : Operand n).write (dataAccess s "store") v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t lin (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
      num_bytes := (n / 8 : Nat) } lin (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull
    ht.cr0 ht.efer.lma ht.lass hcan align
    (by simp only; omega)
    (by
      show AlignmentOk align lin ((n / 8 : Nat) : Int).toNat
      rw [Int.toNat_natCast]; exact halign)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin n)
    .Memory_Write (n / 8) rfl hcount rfl hlow
  have hphys := physicalMemWrite_dataPhysical_run (accessLinear s seg off lin n) lin rfl n
    (by omega) rfl v t ht.smrr ht.cpl hmem
  unfold Logical_Mem_Write
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases nt <;>
  · simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
    rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma),
      specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by decide)),
      specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
        (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
    refine (specM_bind_run _ _ hlin).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (checkDataWriteBreakpoint_run _ _ _ ht.debug)).trans ?_
    refine (specM_bind_run _ _ htr).trans ?_
    try rw [(dataPhysical_translation1 (accessLinear s seg off lin _)).2]
    try simp (config := { decide := true }) only [↓reduceIte]
    exact hphys

/--
A data write of `n` bits (`n` ∈ {8, 16, 32, 64, 128}) at `addr` through a flat data segment, below
4 GiB (it may cross a 4 KiB page), with the bytes present in RAM and the alignment check of `align`
passing (`AlignmentOk`): it is the memory operand's write, plus the bookkeeping
(`dataAccess s "store"`).
-/
theorem logicalMemWrite_run_align [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align addr (n / 8))
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v align false false
      .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_seg_align s h _ addr addr (SegAccess.flat isStack addr) n hn v align halign
    hlow hmem nt

/--
`logicalMemWrite_run_seg_align` for the normal alignment type of the integer instructions, at
`n` ∈ {8, 16, 32, 64}.
-/
theorem logicalMemWrite_run_seg [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) seg off v .Normal_Alignment false false
      .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem lin : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_seg_align s h seg off lin hseg n (by omega) v _ (AlignmentOk.normal _ _)
    hlow hmem nt

/--
`logicalMemWrite_run_align` for the normal alignment type of the integer instructions, at
`n` ∈ {8, 16, 32, 64}.
-/
theorem logicalMemWrite_run [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v .Normal_Alignment false false
      .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_align s h isStack addr n (by omega) v _ (AlignmentOk.normal _ _) hlow
    hmem nt

/--
ENTER's check that the new stack top can be written, `Check_Logical_Address_Is_Writable SS addr n`
for `n` ∈ {8, 16, 32, 64} bits through the flat stack segment as loaded (SS itself, not its null
data segment), with the bytes below
4 GiB: the write permission, canonicality and translation checks of a write pass (the identity
map, page-crossing or not), nothing is written; the bookkeeping is the 464 oracle bits of
`Create_Logical_Address`.
-/
theorem checkLogicalAddressIsWritable_run [Bindings] (s : RamState) (h : DataReady s)
    (hss : s.SS = userStackSegment) (addr : BitVec 64) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (hlow : addr.toNat + n / 8 ≤ 2^32) :
    (Check_Logical_Address_Is_Writable s.SS addr n .Normal_Alignment).run s =
      (.ok (), { s with oracle := oracleSkip s.oracle 464 }) := by
  rw [show (Check_Logical_Address_Is_Writable s.SS addr n .Normal_Alignment).run s =
    (Check_Logical_Address_Is_Writable userStackSegment addr n .Normal_Alignment).run s by
    rw [hss]]
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t addr (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam
    (by omega) hlow
  have hlin := translateLogicalToLinear_run_of_selector t
    { (logicalAddressFromOracle s.oracle userStackSegment s.CPL addr).1 with
      num_bytes := (n / 8 : Nat) }
    (computeLinearAddress_userStackSegment_run t addr ht.efer.lma)
    (show Is_System_Segment userStackSegment = _ by rfl) rfl false
    (show Is_Null_Segment_Selector userStackSegment.selector = _ by rfl) ht.cr0
    ht.efer.lma ht.lass hcan .Normal_Alignment (by simp only; omega)
    (AlignmentOk.normal _ _)
  have htr := translateLinearToPhysical_run_of_dataReady t ht
    { (logicalAddressFromOracle s.oracle userStackSegment s.CPL addr).1 with
      num_bytes := (n / 8 : Nat), linear_address := addr,
      is_implicit_supervisor_mode_access := false } .Memory_Write (n / 8) rfl hcount rfl hlow
  unfold Check_Logical_Address_Is_Writable
  rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma),
    specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by omega)),
    specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
      (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
  refine (specM_bind_run _ _ hlin).trans ?_
  refine (specM_bind_run _ _ htr).trans ?_
  rw [← h.cs]
  rfl

/--
`checkLogicalAddressIsWritable_run` through any segment whose linear address for `off` is `lin`
(`SegAccess`: a flat data segment, or FS or GS after a segment prefix): the checks of a write of `n`
bits (`n` ∈ {8, 16, 32, 64}) at `lin` below 4 GiB pass, page-crossing or not, and nothing is
written; the bookkeeping is the 464 oracle bits of `Create_Logical_Address` (MASKMOVDQU's check of
its 16 bytes before it writes any).
-/
theorem checkLogicalAddressIsWritable_run_seg [Bindings] (s : RamState) (h : DataReady s)
    (seg : Segment) (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (hlow : lin.toNat + n / 8 ≤ 2^32) :
    (Check_Logical_Address_Is_Writable seg off n .Normal_Alignment).run s =
      (.ok (), { s with oracle := oracleSkip s.oracle 464 }) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t lin (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam
    (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
      num_bytes := (n / 8 : Nat) } lin (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull
    ht.cr0 ht.efer.lma ht.lass hcan .Normal_Alignment
    (by simp only; omega) (AlignmentOk.normal _ _)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin n)
    .Memory_Write (n / 8) rfl hcount rfl hlow
  unfold Check_Logical_Address_Is_Writable
  rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma),
    specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by omega)),
    specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
      (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
  refine (specM_bind_run _ _ hlin).trans ?_
  refine (specM_bind_run _ _ htr).trans ?_
  rw [← h.cs]
  rfl

/--
`Check_Logical_Address_Is_Readable seg off 80` (FLD `m80fp`'s check of its 10 bytes before it reads
them) through any segment whose linear address for `off` is `lin` (`SegAccess`), with the bytes
below 4 GiB: the read permission, canonicality and translation checks pass and nothing is read;
the bookkeeping is the 464 oracle bits of `Create_Logical_Address`.
-/
theorem checkLogicalAddressIsReadable80_run_seg [Bindings] (s : RamState) (h : DataReady s)
    (seg : Segment) (off lin : BitVec 64) (hseg : SegAccess seg off lin)
    (hlow : lin.toNat + 10 ≤ 2^32) :
    (Check_Logical_Address_Is_Readable seg off 80).run s =
      (.ok (), { s with oracle := oracleSkip s.oracle 464 }) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcan := isCanonicalWrtPagingMode_run t lin 10 ht.cr0 ht.cr4 ht.efer.lme ht.lam
    (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with num_bytes := 10 } lin
    (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull ht.cr0 ht.efer.lma ht.lass hcan
    .Normal_Alignment (by simp only; omega) (AlignmentOk.normal _ _)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin 80)
    .Memory_Read 10 rfl (by decide) rfl hlow
  unfold Check_Logical_Address_Is_Readable
  rw [specM_bind_run _ _ (checkReadPermission_run _ _ h.cs h.efer.lma)]
  spec_bind_rfl
  spec_bind_rfl!
  spec_bind_rfl
  refine (specM_bind_run _ _ (createLogicalAddress_run80 s seg off)).trans ?_
  rw [specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
      (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
  refine (specM_bind_run _ _ hlin).trans ?_
  refine (specM_bind_run _ _ htr).trans ?_
  rw [← h.cs]
  rfl

/-! ### Locked accesses

A LOCK form (`ADD_LOCK_MEMv_GPRv`, …; XCHG with memory always) reads with `acquire_lock` and
writes with `release_lock`. On this machine the locked access is the unlocked one: the memory
type is write-back (`FetchReady.memoryType`), so `Check_UC_Lock` passes; an access within one
cache line (`InCacheLine`) neither faults in `Check_Split_Lock` nor sets the bus-lock trap in
`Check_Bus_Lock_Trap`, whose CPUID query must be answered; and the machine's
`Unimplemented_Feature` binding is `pure ()` for the lock markers (one core, synchronous RAM).
`LockReady` collects the two facts beyond an unlocked access; `logicalMemRead_run_seg_lock` and
`logicalMemWrite_run_seg_lock` are `logicalMemRead_run_seg` and `logicalMemWrite_run_seg` for the
locked forms. -/

/-- The `len` bytes at `lin` lie in one cache line of the processor's configured line size `c`
(lean-x86's `Is_Cache_Split_Access` is false), and `c` passes lean-x86's configuration check
`1 ≤ c ≤ 2048`, which `Config.Read.Cache_Line_Size` asserts. `InCacheLine.of_aligned`: a
naturally aligned access whose size divides the line size. -/
def InCacheLine [Bindings] (lin : BitVec 64) (len : Nat) : Prop :=
  1 ≤ Bindings.processor.config.Cache_Line_Size ∧ Bindings.processor.config.Cache_Line_Size ≤ 2048 ∧
    (lin.toNat : Int) / Bindings.processor.config.Cache_Line_Size =
      ((lin.toNat + len - 1 : Nat) : Int) / Bindings.processor.config.Cache_Line_Size

/-- An access aligned to its size `len`, which divides the line size `c` (e.g. 1, 2, 4 or 8 bytes
with 64-byte lines), lies in one cache line. -/
theorem InCacheLine.of_aligned [Bindings] {lin : BitVec 64} {len : Nat} (c : Nat)
    (hc : Bindings.processor.config.Cache_Line_Size = c) (h1 : 1 ≤ c) (h2 : c ≤ 2048)
    (hlen : 0 < len) (hdvd : len ∣ c) (halign : lin.toNat % len = 0) : InCacheLine lin len := by
  refine ⟨by rw [hc]; omega, by rw [hc]; omega, ?_⟩
  rw [hc]
  obtain ⟨m, rfl⟩ := hdvd
  obtain ⟨k, hk⟩ : len ∣ lin.toNat := Nat.dvd_of_mod_eq_zero halign
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have e1 : lin.toNat / (len * m) = k / m := by
    rw [← Nat.div_div_eq_div_mul, hk, Nat.mul_div_cancel_left _ hlen]
  have e2 : (lin.toNat + len - 1) / (len * m) = k / m := by
    rw [← Nat.div_div_eq_div_mul, hk]
    congr 1
    rw [show len * k + len - 1 = (len - 1) + len * k by omega, Nat.add_mul_div_left _ _ hlen,
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [← Int.natCast_ediv, ← Int.natCast_ediv, e1, e2]

/-- What a locked access of `len` bytes at linear address `lin` needs beyond the unlocked one: it
lies in one cache line (`InCacheLine`: no split lock, so no #AC from `Check_Split_Lock` and no
bus-lock debug trap), and the CPUID query of `Check_Bus_Lock_Trap` (bus-lock detection) is
answered. -/
structure LockReady [Bindings] (s : RamState) (lin : BitVec 64) (len : Nat) : Prop where
  line : InCacheLine lin len
  busLock : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_BUS_LOCK_DETECT_Encoding b

/-- `LockReady` depends on the state only through its CPUID answer, which `SameControls` keeps. -/
theorem LockReady.of_sameControls [Bindings] {s t : RamState} {lin : BitVec 64} {len : Nat}
    (h : LockReady s lin len) (hst : SameControls s t) : LockReady t lin len :=
  ⟨h.line, h.busLock.imp fun _ => reportsCPUFeature_of_sameControls hst⟩

/-- An access of `n` bits within one cache line does not split one. -/
theorem isCacheSplitAccess_of_inCacheLine [Bindings] {lin : BitVec 64} {n : Nat} (hn : 8 ≤ n)
    (h8 : n % 8 = 0) (h : InCacheLine lin (n / 8)) : Is_Cache_Split_Access lin n = .ok false := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (Config.Value.Cache_Line_Size.value : Int) =
      Bindings.processor.config.Cache_Line_Size := rfl
  unfold Is_Cache_Split_Access Config.Read.Cache_Line_Size Config.Check.Cache_Line_Size
  rw [hv]
  generalize Bindings.processor.config.Cache_Line_Size = c at h1 h2 h3
  have h8' : ((n : Int) / 8) = ((n / 8 : Nat) : Int) := by omega
  have hend : (lin.toNat : Int) + (n / 8 : Nat) - 1 = ((lin.toNat + n / 8 - 1 : Nat) : Int) := by
    omega
  have hc : X86.Runtime.inRange c 1 2048 = true := by simp [inRange_eq, h1, h2]
  have hlt : (0 : Int) < c := by omega
  simp only [assert_of_true hc, assert_of_true (show decide (0 < c) = true by simp [hlt]),
    stdPositiveDivide_eq_pure (show (0 : Int) ≤ n by omega) (show (0 : Int) < 8 by decide),
    unsigned_eq, bind, pure, Except.bind, Except.pure, h8', hend,
    assert_of_true (show decide (0 ≤ ((lin.toNat : Nat) : Int)) = true by simp),
    assert_of_true (show decide (0 ≤ ((lin.toNat + n / 8 - 1 : Nat) : Int)) = true by simp),
    stdPositiveDivide_eq_pure (show (0 : Int) ≤ ((lin.toNat : Nat) : Int) by omega) hlt,
    stdPositiveDivide_eq_pure (show (0 : Int) ≤ ((lin.toNat + n / 8 - 1 : Nat) : Int) by omega) hlt,
    h3, bne_self_eq_false]

/-- `Check_UC_Lock` passes on write-back memory. -/
theorem checkUCLock_run_wb [Bindings] (s : RamState) :
    (Check_UC_Lock (σ := Ram) .Memory_Type_Write_Back).run s = (.ok (), s) := rfl

/-- `Check_Split_Lock` passes for an access within one cache line. -/
theorem checkSplitLock_run [Bindings] (s : RamState) {pa : BitVec 64} {n : Nat} (hn : 8 ≤ n)
    (h8 : n % 8 = 0) (h : InCacheLine pa (n / 8)) :
    (Check_Split_Lock (σ := Ram) pa n).run s = (.ok (), s) := by
  unfold Check_Split_Lock
  rw [specM_bind_run _ _ (liftM_run_of_ok (isCacheSplitAccess_of_inCacheLine hn h8 h) s)]
  rfl

/-- `Check_Bus_Lock_Trap` does nothing for a write-back access within one cache line (once its
CPUID query is answered). -/
theorem checkBusLockTrap_run [Bindings] (s : RamState) {pa : BitVec 64} {n : Nat} (hn : 8 ≤ n)
    (h8 : n % 8 = 0) (h : InCacheLine pa (n / 8))
    (hbus : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_BUS_LOCK_DETECT_Encoding b) :
    (Check_Bus_Lock_Trap (σ := Ram) pa n .Memory_Type_Write_Back).run s = (.ok (), s) := by
  obtain ⟨b, hb⟩ := hbus
  have hc : (CPUID_BUS_LOCK_DETECT : X86.Runtime.SpecM X86.Exception RamState Bool).run s =
      (.ok b, s) := by
    unfold CPUID_BUS_LOCK_DETECT
    exact readCPUIDFeature_run hb
  unfold Check_Bus_Lock_Trap
  rw [specM_bind_run _ _ hc]
  cases b
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    split
    · rw [specM_bind_run _ _ (liftM_run_of_ok (isCacheSplitAccess_of_inCacheLine hn h8 h) s)]
      rfl
    · rfl

/-- The machine's `Unimplemented_Feature` is `pure ()` for the lock markers. -/
theorem unimplementedFeature_lock_run (s : RamState) (name : String)
    (h : name = "Logical_Mem_Read(acquire_lock=>True)" ∨
      name = "Logical_Mem_Write(release_lock=>True)" ∨ name = "LockedMemRead") :
    (Unimplemented_Feature (σ := Ram) name true false).run s = (.ok (), s) := by
  rcases h with rfl | rfl | rfl <;> rfl

/--
`logicalMemRead_run_seg` for a locked read (`acquire_lock`, a read-modify-write's), given
`LockReady`: the same value and bookkeeping as the unlocked read; also at 128 bits (LOCK
CMPXCHG16B, whose locked form has the normal alignment type).
-/
theorem logicalMemRead_run_seg_lock [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hlock : LockReady s lin (n / 8)) :
    (Logical_Mem_Read seg off n .Memory_Read_Modify_Write .Normal_Alignment true).run s =
      (.ok ((Operand.mem lin : Operand n).read s), dataAccess s "load") := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hlt : LockReady t lin (n / 8) :=
    hlock.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t lin (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
      num_bytes := (n / 8 : Nat) } lin (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull
    ht.cr0 ht.efer.lma ht.lass hcan .Normal_Alignment
    (by simp only; omega)
    (by
      show AlignmentOk .Normal_Alignment lin ((n / 8 : Nat) : Int).toNat
      exact AlignmentOk.normal _ _)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin n)
    .Memory_Read_Modify_Write (n / 8) rfl hcount rfl hlow
  have hphys := physicalMemRead_dataPhysical_run (accessLinear s seg off lin n) lin rfl n
    (by omega) rfl t ht.smrr ht.cpl hmem
  obtain ⟨hpa, hmt⟩ := dataPhysical_translation1 (accessLinear s seg off lin n)
  have hpa' : (dataPhysical (accessLinear s seg off lin n)).translation1.physical_address = lin :=
    hpa
  unfold Logical_Mem_Read
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
    rw [specM_bind_run _ _ (checkReadPermission_run _ _ h.cs h.efer.lma)]
    rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma)]
    rw [specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by decide)),
      specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
        (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
    refine (specM_bind_run _ _ hlin).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (checkDataReadBreakpoint_run _ _ _ ht.debug)).trans ?_
    refine (specM_bind_run _ _ htr).trans ?_
    rw [hmt, hpa']
    spec_run [Check_UC_Lock => checkUCLock_run_wb t,
      Check_Split_Lock => checkSplitLock_run t (by decide) (by decide) hlt.line,
      Check_Bus_Lock_Trap => checkBusLockTrap_run t (by decide) (by decide) hlt.line hlt.busLock,
      liftM => liftM_run_of_ok (isAligned_eq lin (by decide)) t]
    split <;>
    · spec_run [Unimplemented_Feature => unimplementedFeature_lock_run t _ (by simp),
        Physical_Mem_Read => hphys]

/--
`logicalMemWrite_run_seg` for a locked write (`release_lock`): the same write as the unlocked one
(also at 128 bits, LOCK CMPXCHG16B).
-/
theorem logicalMemWrite_run_seg_lock [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Write (size := n) seg off v .Normal_Alignment true false .Memory_Type_Unknown
      false).run s = (.ok (), (Operand.mem lin : Operand n).write (dataAccess s "store") v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t lin (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
      num_bytes := (n / 8 : Nat) } lin (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull
    ht.cr0 ht.efer.lma ht.lass hcan .Normal_Alignment
    (by simp only; omega)
    (by
      show AlignmentOk .Normal_Alignment lin ((n / 8 : Nat) : Int).toNat
      exact AlignmentOk.normal _ _)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin n)
    .Memory_Write (n / 8) rfl hcount rfl hlow
  have hphys := physicalMemWrite_dataPhysical_run (accessLinear s seg off lin n) lin rfl n
    (by omega) rfl v t ht.smrr ht.cpl hmem
  unfold Logical_Mem_Write
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
    rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma),
      specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by decide)),
      specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
        (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
    refine (specM_bind_run _ _ hlin).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (checkDataWriteBreakpoint_run _ _ _ ht.debug)).trans ?_
    refine (specM_bind_run _ _ htr).trans ?_
    spec_run [Unimplemented_Feature => unimplementedFeature_lock_run t _ (by simp),
      Physical_Mem_Write => hphys]

/-! ### What a write changes -/

theorem memStore_eq_foldl (m : Ram) (addr : BitVec 64) {n : Nat} (v : BitVec n) :
    memStore m addr v = (List.range (n / 8)).foldl (fun m i =>
      m.insert (addr + BitVec.ofNat 64 i) (UInt8.ofNat (v.toNat >>> (8 * i)))) m := rfl

/-- The byte of `v` that `memStore` puts at offset `i`. -/
def storedByte {n : Nat} (v : BitVec n) (i : Nat) : UInt8 := UInt8.ofNat (v.toNat >>> (8 * i))

private theorem foldl_insert_of_ne (items : List Nat) (addr : BitVec 64) (b : Nat → UInt8)
    (m : Ram) (x : BitVec 64) (hx : ∀ i ∈ items, addr + BitVec.ofNat 64 i ≠ x) :
    (items.foldl (fun m i => m.insert (addr + BitVec.ofNat 64 i) (b i)) m)[x]? = m[x]? := by
  induction items generalizing m with
  | nil => rfl
  | cons j items ih =>
    rw [List.foldl_cons, ih _ fun i hi => hx i (List.mem_cons_of_mem _ hi),
      Std.ExtHashMap.getElem?_insert]
    simp [hx j List.mem_cons_self]

private theorem foldl_insert_self (items : List Nat) (addr : BitVec 64) (b : Nat → UInt8)
    (m : Ram) (i : Nat) (hi : i ∈ items)
    (hinj : ∀ j ∈ items, addr + BitVec.ofNat 64 j = addr + BitVec.ofNat 64 i → j = i) :
    (items.foldl (fun m i => m.insert (addr + BitVec.ofNat 64 i) (b i)) m)[addr +
      BitVec.ofNat 64 i]? = some (b i) := by
  induction items generalizing m with
  | nil => simp at hi
  | cons j items ih =>
    rw [List.foldl_cons]
    by_cases hrest : i ∈ items
    · exact ih _ hrest fun k hk => hinj k (List.mem_cons_of_mem _ hk)
    · have hj : j = i := by
        rcases List.mem_cons.mp hi with h | h
        · exact h.symm
        · exact absurd h hrest
      subst hj
      rw [foldl_insert_of_ne _ _ _ _ _ fun k hk he => hrest (hinj k (List.mem_cons_of_mem _ hk) he ▸ hk)]
      simp

/-- A byte outside the written range is unchanged. -/
theorem memStore_getElem?_of_ne (m : Ram) (addr : BitVec 64) {n : Nat} (v : BitVec n)
    (x : BitVec 64) (hx : ∀ i, i < n / 8 → addr + BitVec.ofNat 64 i ≠ x) :
    (memStore m addr v)[x]? = m[x]? :=
  foldl_insert_of_ne _ _ _ _ _ fun i hi => hx i (List.mem_range.mp hi)

theorem add_ofNat_inj (addr : BitVec 64) {i j : Nat} (hi : i < 2^64) (hj : j < 2^64)
    (h : addr + BitVec.ofNat 64 j = addr + BitVec.ofNat 64 i) : j = i := by
  have h' := congrArg BitVec.toNat ((BitVec.add_right_inj addr).mp h)
  simp only [BitVec.toNat_ofNat] at h'
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'

/-- Byte `i` of the written range holds byte `i` of the value. -/
theorem memStore_getElem?_self (m : Ram) (addr : BitVec 64) {n : Nat} (v : BitVec n)
    (hn : n ≤ 128) (i : Nat) (hi : i < n / 8) :
    (memStore m addr v)[addr + BitVec.ofNat 64 i]? = some (storedByte v i) :=
  foldl_insert_self _ _ _ _ _ (List.mem_range.mpr hi) fun j hj he =>
    add_ofNat_inj addr (by omega) (by have := List.mem_range.mp hj; omega) he

/-- `memStore_getElem?_self` for a store of at most `2^64` bytes (a `REP` string store), which
writes each address once. -/
theorem memStore_getElem?_self_of_le (m : Ram) (addr : BitVec 64) {n : Nat} (v : BitVec n)
    (hn : n / 8 ≤ 2 ^ 64) (i : Nat) (hi : i < n / 8) :
    (memStore m addr v)[addr + BitVec.ofNat 64 i]? = some (storedByte v i) :=
  foldl_insert_self _ _ _ _ _ (List.mem_range.mpr hi) fun j hj he =>
    add_ofNat_inj addr (by omega) (by have := List.mem_range.mp hj; omega) he

/-- A byte that a store covers holds the stored byte of the last offset at it: a store of more
than 2^64 bytes wraps around and writes some addresses more than once. -/
theorem memStore_getElem?_cover (m : Ram) (addr : BitVec 64) {n : Nat} (v : BitVec n)
    (x : BitVec 64) (hx : ∃ i < n / 8, addr + BitVec.ofNat 64 i = x) :
    ∃ j < n / 8, addr + BitVec.ofNat 64 j = x ∧
      (memStore m addr v)[x]? = some (storedByte v j) := by
  rw [memStore_eq_foldl]
  generalize n / 8 = k at hx ⊢
  induction k with
  | zero => obtain ⟨i, hi, -⟩ := hx; omega
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hk : addr + BitVec.ofNat 64 k = x
    · exact ⟨k, by omega, hk, by simp [hk, storedByte]⟩
    · obtain ⟨i, hi, hix⟩ := hx
      obtain ⟨j, hj, hjx, hv⟩ := ih ⟨i, by have : i ≠ k := fun h => hk (h ▸ hix); omega, hix⟩
      exact ⟨j, by omega, hjx, by simpa [Std.ExtHashMap.getElem?_insert, hk] using hv⟩

/-- A write keeps every byte of RAM present. -/
theorem memStore_isSome (m : Ram) (addr : BitVec 64) {n : Nat} (v : BitVec n) (x : BitVec 64)
    (h : (m[x]?).isSome) : ((memStore m addr v)[x]?).isSome := by
  rw [memStore_eq_foldl]
  generalize List.range (n / 8) = items
  induction items generalizing m with
  | nil => exact h
  | cons j items ih =>
    apply ih
    rw [Std.ExtHashMap.getElem?_insert]
    split <;> simp_all

/--
A write that lies below 4 GiB and holds none of the page-table entries (`PageTableEntriesApart`:
the eight bytes at `0x1000` and the 32 at `0x2000`) keeps `Prelude`'s identity page tables.
-/
theorem IdentityPageTableMemory.memStore {m : Ram} (h : IdentityPageTableMemory m)
    (addr : BitVec 64) {n : Nat} (v : BitVec n) (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart addr.toNat (n / 8)) :
    IdentityPageTableMemory (X86Proofs.memStore m addr v) := by
  have hf (x : Nat) (hx : ¬ PageTableEntriesApart x 1) :
      (X86Proofs.memStore m addr v)[BitVec.ofNat 64 x]? = m[BitVec.ofNat 64 x]? := by
    apply memStore_getElem?_of_ne
    intro i hi he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  refine ⟨fun i => ?_, fun page i => ?_⟩
  · rw [hf _ (by have := i.isLt; omega)]; exact h.1 i
  · rw [hf _ (by have := i.isLt; have := page.isLt; omega)]; exact h.2 page i


/-- A one-byte memory operand is the byte. -/
theorem memLoad_8 (m : Ram) (addr : BitVec 64) : memLoad m addr 8 = (memByte m addr).toBitVec := by
  simp [memLoad]

/-- Reading back a one-byte write. -/
theorem memLoad_memStore_8 (m : Ram) (addr : BitVec 64) (v : BitVec 8) :
    memLoad (memStore m addr v) addr 8 = v := by
  rw [memLoad_8, memByte]
  have := memStore_getElem?_self m addr v (by decide) 0 (by decide)
  rw [show addr + BitVec.ofNat 64 0 = addr from BitVec.add_zero addr] at this
  simp [PhysicalMemory.read, this, storedByte]

/-- Every state a step passes through before memory changes has the data-access facts. -/
theorem ReadyToStep.dataReady [Bindings] {s : RamState} (h : ReadyToStep s) : DataReady s :=
  { cs := h.cpu.cs, cr0 := h.cpu.cr0, cr3 := h.memory.cr3, cr4 := h.cpu.cr4, efer := h.cpu.efer,
    maxPhysical := h.cpu.maxPhysical, early := h.cpu.early, lam := h.cpu.lam, lass := h.cpu.lass,
    cetSS := h.features.cetSS, smrr := h.smrr, memoryType := h.memoryType,
    tables := h.memory.tables, cpl := h.cpu.cpl, debug := h.cpu.debug }

end X86Proofs
