import X86Proofs.Core.ReadOnly
import X86Proofs.Core.Mode
import Prelude

/-!
# Paging and physical memory

What address translation and physical reads do on a `RamState` whose control registers are
`Prelude`'s supported integer configuration and whose page tables are `Prelude`'s identity map of
the low 4 GiB: for any access (fetch, read, write, read-modify-write), every linear address below
2^32 translates to itself with write-back memory type, without changing the state. The SMRR and
memory-type facts are `Prelude`'s `SMRRUnblocked` and `WriteBackMemoryType` for the bindings in
use.

Writes take one more step in the page walk: lean-x86 reads CPUID.CET_SS and rechecks the access
rights to decide whether to set the dirty bit of the 1 GiB page entry, then calls
`Page_AD_Bit_Update`. The identity map's entries already have the accessed and dirty bits set
(`0xe7`), so that update returns at once and writes nothing (`pageADBitUpdate_e7_run`); the walk
only needs the CPUID read to succeed (`hcet`).

An access that crosses a 4 KiB page is translated as two (`translateLinearToPhysical_run_of_split`): the bytes
up to the end of the first page (`firstPageAccess`) and the rest (`secondPageAccess`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers
open scoped X86.Runtime.Syntax

/-! `Prelude`'s CR0 and CR4 facts are stated with lean-x86's field accessors (`cr0.PE = 1`). After
lean-x86's register reads are unfolded, goals mention the bit slice itself (`cr0.extractLsb' 0 1`),
so these restate the fields in that form for `simp`. -/

theorem supportedIntegerCR0_extractLsb_pe {cr0 : X86.CR0_Type} (h : Prelude.SupportedIntegerCR0 cr0) :
    cr0.extractLsb' 0 1 = 1 := h.pe

theorem supportedIntegerCR0_extractLsb_am {cr0 : X86.CR0_Type} (h : Prelude.SupportedIntegerCR0 cr0) :
    cr0.extractLsb' 18 1 = 0 := h.am

theorem supportedIntegerCR0_extractLsb_pg {cr0 : X86.CR0_Type} (h : Prelude.SupportedIntegerCR0 cr0) :
    cr0.extractLsb' 31 1 = 1 := h.pg

theorem supportedIntegerCR4_extractLsb_pae {cr4 : X86.CR4_Type} (h : Prelude.SupportedIntegerCR4 cr4) :
    cr4.extractLsb' 5 1 = 1 := h.pae

theorem supportedIntegerCR4_extractLsb_la57 {cr4 : X86.CR4_Type} (h : Prelude.SupportedIntegerCR4 cr4) :
    cr4.extractLsb' 12 1 = 0 := h.la57

theorem supportedIntegerCR4_extractLsb_smep {cr4 : X86.CR4_Type} (h : Prelude.SupportedIntegerCR4 cr4) :
    cr4.extractLsb' 20 1 = 0 := h.smep

theorem supportedIntegerCR4_extractLsb_smap {cr4 : X86.CR4_Type} (h : Prelude.SupportedIntegerCR4 cr4) :
    cr4.extractLsb' 21 1 = 0 := h.smap

theorem supportedIntegerCR4_extractLsb_pke {cr4 : X86.CR4_Type} (h : Prelude.SupportedIntegerCR4 cr4) :
    cr4.extractLsb' 22 1 = 0 := h.pke

theorem supportedIntegerCR4_extractLsb_cet {cr4 : X86.CR4_Type} (h : Prelude.SupportedIntegerCR4 cr4) :
    cr4.extractLsb' 23 1 = 0 := h.cet

theorem isCanonicalWrtPosition48_run_of_low32 (address : BitVec 64)
    (h : address.toNat < 2^32) :
    Is_Canonical_Wrt_Position address 48 = .ok true := by
  change (if BitVec.extractLsb' 47 1 address == (0 : BitVec 1)
    then Except.ok (BitVec.extractLsb' 48 16 address == (0 : BitVec 16))
    else Except.ok (BitVec.extractLsb' 48 16 address == BitVec.allOnes 16)) = _
  have bit47 : BitVec.extractLsb' 47 1 address = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat]
    have : address.toNat / 2^47 = 0 := Nat.div_eq_of_lt (by omega)
    simp [Nat.shiftRight_eq_div_pow, this]
  have bits48 : BitVec.extractLsb' 48 16 address = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat]
    have : address.toNat / 2^48 = 0 := Nat.div_eq_of_lt (by omega)
    simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow, this, Nat.zero_mod, BitVec.ofNat_eq_ofNat,
      BitVec.toNat_ofNat]
  simp only [bit47, BitVec.ofNat_eq_ofNat, BEq.rfl, ↓reduceIte, bits48]

noncomputable def translationFromOracle (o : X86.Runtime.Oracle) (la pa : BitVec 64) (mt : Memory_Type) :
    Translation × X86.Runtime.Oracle :=
  let (guest, o) := o.take 64
  let (write, o) := o.take 1
  let (user, o) := o.take 1
  let (execute, o) := o.take 1
  let (shadow, o) := o.take 1
  let (valid, o) := o.take 1
  let (pat, o) := o.take 3
  ({ size_in_bytes := 0, linear_address := la, guest_physical_address := guest,
     physical_address := pa, is_write_allowed := write.getLsbD 0,
     is_user_mode_address := user.getLsbD 0, is_execute_disabled := execute.getLsbD 0,
     is_shadow_stack_address := shadow.getLsbD 0, is_guest_physical_address_valid := valid.getLsbD 0,
     page_pat_pcd_pwt := pat, memory_type := mt }, o)

theorem isLinearAccessSplitAcross4KBPages_run {σ : Type} (s : X86.State σ) (address : BitVec 64)
    (numBytes : Int) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hnum : 0 < numBytes) :
    (Is_Linear_Access_Split_Across4KB_Pages address numBytes).run s =
      (.ok (decide (4096 < (address.toNat : Int) % 4096 + numBytes)), s) := by
  have hn : 1 ≤ (address.toNat : Int) + numBytes := by omega
  simp [Is_Linear_Access_Split_Across4KB_Pages, cr0PG_eq, get, getThe, liftM, bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, MonadStateOf.get, monadLift,
    MonadLift.monadLift, pure, ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map,
    StateT.map, Bind.bind, Pure.pure, x86_runtime, (supportedIntegerCR0_extractLsb_pg hcr0), hn]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, decide_eq_true_eq]
  omega

theorem isLinearAccessSplitAcross4KBPages_run_of_fits {σ : Type} (s : X86.State σ) (address : BitVec 64)
    (numBytes : Int) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hnum : 0 < numBytes)
    (hfit : (address.toNat : Int) % 4096 + numBytes ≤ 4096) :
    (Is_Linear_Access_Split_Across4KB_Pages address numBytes).run s = (.ok false, s) := by
  rw [isLinearAccessSplitAcross4KBPages_run s address numBytes hcr0 hnum]
  simp only [show ¬4096 < (address.toNat : Int) % 4096 + numBytes from by omega, decide_false]

noncomputable def singleTranslation (linear : Address_Translation) (translation : Translation) : Address_Translation :=
  {linear with is_split_access := false, translation1 := translation}

theorem translateLinearToPhysical_run [instBindings : X86.Machine.Bindings]
    (s t : RamState) (linear : Address_Translation)
    (access : Memory_Access_Type) (translation : Translation)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0)
    (hsplit : (Is_Linear_Access_Split_Across4KB_Pages linear.linear_address linear.num_bytes).run s =
      (.ok false, s))
    (htranslate : (Translate linear access).run s = (.ok translation, t)) :
    (Translate_Linear_To_Physical linear access).run s =
      (.ok (singleTranslation linear translation), t) := by
  have hpg : (X86.CR0.PG : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 1, s) := by
    rw [cr0PG_run, supportedIntegerCR0_extractLsb_pg hcr0]
  have hpe : (X86.CR0.PE : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 1, s) := by
    rw [cr0PE_run, supportedIntegerCR0_extractLsb_pe hcr0]
  unfold Translate_Linear_To_Physical
  rw [specM_bind_run _ _ hpg]
  simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ hpe]
  simp only [BitVec.reduceBEq, x86_runtime, pure_bind]
  rw [specM_bind_run _ _ hsplit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ htranslate]
  rfl

theorem isLinearAccessSplitAcross4KBPages_run_of_crosses {σ : Type} (s : X86.State σ) (address : BitVec 64)
    (numBytes : Int) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0) (hnum : 0 < numBytes)
    (hcross : 4096 < (address.toNat : Int) % 4096 + numBytes) :
    (Is_Linear_Access_Split_Across4KB_Pages address numBytes).run s = (.ok true, s) := by
  rw [isLinearAccessSplitAcross4KBPages_run s address numBytes hcr0 hnum]
  simp only [hcross, decide_true]

/-- The bytes from `address` to the end of its 4 KiB page (1 to 4096). -/
def pageHeadBytes (address : BitVec 64) : Int :=
  4096 - (address.toNat : Int) % 4096

/-- The part of a page-crossing access in its first page. -/
def firstPageAccess (linear : Address_Translation) : Address_Translation :=
  {linear with num_bytes := pageHeadBytes linear.linear_address}

/-- The part of a page-crossing access in its second page. -/
def secondPageAccess (linear : Address_Translation) : Address_Translation :=
  {linear with
    linear_address :=
      BitVec.add linear.linear_address (BitVec.ofInt 64 (pageHeadBytes linear.linear_address))
    num_bytes := linear.num_bytes - pageHeadBytes linear.linear_address}

noncomputable def splitTranslation (linear : Address_Translation) (first second : Translation) :
    Address_Translation :=
  {linear with is_split_access := true, translation1 := first, translation2 := second}

/--
A page-crossing access translates its two parts separately (`firstPageAccess`,
`secondPageAccess`) and keeps both translations.
-/
theorem translateLinearToPhysical_run_of_split [instBindings : X86.Machine.Bindings]
    (s t u : RamState) (linear : Address_Translation)
    (access : Memory_Access_Type) (first second : Translation)
    (hcr0 : Prelude.SupportedIntegerCR0 s.CR0)
    (hsplit : (Is_Linear_Access_Split_Across4KB_Pages linear.linear_address linear.num_bytes).run s =
      (.ok true, s))
    (hfirst : (Translate (firstPageAccess linear) access).run s = (.ok first, t))
    (hsecond : (Translate (secondPageAccess linear) access).run t = (.ok second, u)) :
    (Translate_Linear_To_Physical linear access).run s =
      (.ok (splitTranslation linear first second), u) := by
  have hpg : (X86.CR0.PG : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 1, s) := by
    rw [cr0PG_run, supportedIntegerCR0_extractLsb_pg hcr0]
  have hpe : (X86.CR0.PE : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 1, s) := by
    rw [cr0PE_run, supportedIntegerCR0_extractLsb_pe hcr0]
  unfold Translate_Linear_To_Physical
  rw [specM_bind_run _ _ hpg]
  simp only [BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ hpe]
  simp only [BitVec.reduceBEq, x86_runtime, pure_bind]
  rw [specM_bind_run _ _ hsplit]
  simp only [↓reduceIte]
  change (do
    let tr1 ← Translate (firstPageAccess linear) access
    let tr2 ← Translate (secondPageAccess linear) access
    pure (splitTranslation linear tr1 tr2) :
      X86.Runtime.SpecM X86.Exception RamState Address_Translation).run s = _
  rw [specM_bind_run _ _ hfirst, specM_bind_run _ _ hsecond]
  rfl

theorem smrrBlocked_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s) (address : BitVec 64) :
    Bindings.MemoryType.smrrBlocked s address = .ok false := by
  unfold Bindings.MemoryType.smrrBlocked
  have h : X86.Helpers.Emulate_Memory.SMRR_Matches instBindings.memoryType.mtrrCap
      s.IA32_SMRR_PHYSBASE s.IA32_SMRR_PHYSMASK address = .ok false := hsmrr address
  rw [h]
  rfl

theorem readPhysicalByte_run [instBindings : X86.Machine.Bindings]
    {exception : Type} (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (address : BitVec 64) (byte : UInt8) (h : s.external[address]? = some byte) :
    (Bindings.PhysicalAccess.readPhysicalByte (exception := exception) address).run s =
      (.ok byte, s) := by
  unfold Bindings.PhysicalAccess.readPhysicalByte
  simp only [smrrBlocked_run s hsmrr, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, StateT.get, pure, ExceptT.bindCont,
    StateT.pure, Except.mapError, Bool.false_eq_true, ↓reduceIte, PhysicalMemory.read, h, ExceptT.pure]

theorem byteCount_run {exception : Type} (count : Nat) (s : RamState) :
    (Bindings.PhysicalAccess.byteCount (exception := exception) (8 * count)).run s =
      (.ok count, s) := by
  have hnonneg : ¬ (8 * (count : Int) < 0) := by omega
  simp [Bindings.PhysicalAccess.byteCount, hnonneg, Int.mul_ediv_cancel_left]

noncomputable def assembleBytes (size : Int) (count : Nat) (bytes : Nat → UInt8) : BitVec size.toNat :=
  (List.range count).foldl (fun result i =>
    result ||| (BitVec.ofNat size.toNat (bytes i).toNat <<< (8 * i))) 0

theorem readBytes_run [instBindings : X86.Machine.Bindings]
    {exception : Type} (count : Nat) (address : Nat → BitVec 64)
    (bytes : Nat → UInt8) (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (h : ∀ i, i < count → s.external[address i]? = some (bytes i)) :
    (Bindings.PhysicalAccess.readBytes (exception := exception) (8 * count) address).run s =
      (.ok (assembleBytes (8 * count) count bytes), s) := by
  unfold Bindings.PhysicalAccess.readBytes
  rw [specM_bind_run _ _ (byteCount_run count s)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hloop := specM_forIn_run (exception := exception) (List.range count)
    (fun i acc => do
      let byte ← Bindings.PhysicalAccess.readPhysicalByte (σ := Ram) (exception := exception) (address i)
      pure (.yield (acc ||| (BitVec.ofNat (8 * (count : Int)).toNat byte.toNat <<< (8 * i)))))
    (fun i acc => acc ||| (BitVec.ofNat (8 * (count : Int)).toNat (bytes i).toNat <<< (8 * i))) s 0
    (by
      intro i hi acc
      rw [specM_bind_run _ _ (readPhysicalByte_run s hsmrr (address i) (bytes i) (h i (by simpa using hi)))]
      rfl)
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range'] at *
  rw [specM_bind_run _ _ hloop]
  rfl

/-- `byteCount n` for a whole number of bytes, `n` as a `Nat` cast. -/
theorem byteCount_run_nat {exception : Type} (n : Nat) (hn : n % 8 = 0) (s : RamState) :
    (Bindings.PhysicalAccess.byteCount (σ := Ram) (exception := exception) (n : Int)).run s =
      (.ok (n / 8), s) := by
  have h1 : (decide ((n : Int) < 0) || ((n : Int) % 8 != 0)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq]
    omega
  have h3 : ((n : Int) / 8).toNat = n / 8 := by omega
  unfold Bindings.PhysicalAccess.byteCount
  simp only [h1, Bool.false_eq_true, ↓reduceIte, h3]
  rfl

/-- `readBytes_run` with the size as a `Nat` cast (a multiple of 8). -/
theorem readBytes_run_nat [instBindings : Bindings] {exception : Type} (n : Nat) (hn : n % 8 = 0)
    (address : Nat → BitVec 64) (bytes : Nat → UInt8) (s : RamState)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (h : ∀ i, i < n / 8 → s.external[address i]? = some (bytes i)) :
    (Bindings.PhysicalAccess.readBytes (σ := Ram) (exception := exception) (n : Int) address).run s =
      (.ok (assembleBytes n (n / 8) bytes), s) := by
  unfold Bindings.PhysicalAccess.readBytes
  rw [specM_bind_run _ _ (byteCount_run_nat n hn s)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hloop := specM_forIn_run (exception := exception) (List.range (n / 8))
    (fun i acc => do
      let byte ← Bindings.PhysicalAccess.readPhysicalByte (σ := Ram) (exception := exception)
        (address i)
      pure (.yield (acc ||| (BitVec.ofNat (n : Int).toNat byte.toNat <<< (8 * i)))))
    (fun i acc => acc ||| (BitVec.ofNat (n : Int).toNat (bytes i).toNat <<< (8 * i))) s 0
    (by
      intro i hi acc
      rw [specM_bind_run _ _ (readPhysicalByte_run s hsmrr (address i) (bytes i)
        (h i (by simpa using hi)))]
      rfl)
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range'] at *
  rw [specM_bind_run _ _ hloop]
  rfl

/--
The accessed/dirty-bit update on an identity-map entry (low byte `0xe7`: A and D already set) is a
no-op, whether or not the walk asks for the dirty bit.
-/
theorem pageADBitUpdate_e7_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (la pa : BitVec 64)
    (pat : BitVec 3) (level : Paging_Level_Type) (dirty : Bool) :
    (Page_AD_Bit_Update la pa pat 0xe7 level dirty).run s = (.ok (), s) := by
  cases dirty <;> rfl

theorem isEPTEnabled_run (s : RamState) :
    Is_EPT_Enabled.run s = (.ok false, s) := by
  change (Except.ok (strictAnd (s.VMX_Operation_Mode == .VMX_Non_Root) false), s) = _
  cases s.VMX_Operation_Mode <;> rfl

private theorem strictAnd_false (b : Bool) : strictAnd b false = false := by
  cases b <;> rfl

theorem hlatIsAddressEnabled_run (s : RamState) (address : BitVec 64) :
    (HLAT.Is_Address_Enabled address).run s = (.ok false, s) := by
  unfold HLAT.Is_Address_Enabled
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map,
    StateT.get, pure, ExceptT.bindCont, VM_Exec_Controls3, liftNoSourceException_eq, ExceptT.adapt,
    VM_Exec_Controls3.Binding.call, ExceptT.pure, StateT.pure, BitVec.ofNat_eq_ofNat, Int.toNat_one,
    Except.mapError, HAnd.hAnd, AndOp.and, BitVec.reduceBEq, strictAnd_false, Bool.false_eq_true,
    ↓reduceIte]

theorem physicalMemReadPTW64_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s) (la pa : BitVec 64)
    (pat : BitVec 3) (level : Paging_Level_Type) (bytes : Nat → UInt8)
    (h : ∀ i, i < 8 → s.external[pa + BitVec.ofNat 64 i]? = some (bytes i)) :
    (Physical_Mem_Read_PTW la pa 64 pat level).run s =
      (.ok (assembleBytes 64 8 bytes), s) := by
  have hext : (Physical_Mem_Read_PTW.Binding.call la pa 64 pat level :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run s =
      (.ok (assembleBytes 64 8 bytes), s) := by
    refine (specM_bind_run _ _ (isEPTEnabled_run s)).trans ?_
    exact readBytes_run 8 _ bytes s hsmrr h
  unfold Physical_Mem_Read_PTW
  simp only [x86_runtime, show (0 : Int) ≤ 64 by decide, decide_true]
  simp only [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.run,
    ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch]
  change Physical_Mem_Read_PTW.Binding.call la pa 64 pat level s = _ at hext
  rw [hext]
  rfl


noncomputable def IdentityPageTableMemory (memory : Ram) : Prop :=
  (∀ i : Fin 8, memory[BitVec.ofNat 64 (0x1000 + i.val)]? =
    some (UInt8.ofNat ((0x2027 : Nat) >>> (8 * i.val) % 256))) ∧
  (∀ page : Fin 4, ∀ i : Fin 8,
    memory[BitVec.ofNat 64 (0x2000 + 8 * page.val + i.val)]? =
      some (UInt8.ofNat (((page.val <<< 30 ||| 0xe7) : Nat) >>> (8 * i.val) % 256)))

/-- The `len` bytes at `a` hold none of the page-table entries `IdentityPageTableMemory` fixes: the
PML4 entry at `[0x1000, 0x1008)` and the four PDPT entries at `[0x2000, 0x2020)`. The rest of their
two frames (`[0x1008, 0x2000)` and `[0x2020, 0x3000)`) is ordinary memory: `Prelude`'s
`IdentityMappedMemory` says nothing of it, so a write may change it. Unlike `RangeApart`, it takes
the address as a number (a guard writes `a.toNat`) and is an `abbrev`, so that `omega` and `decide`
read it as the comparisons it is. -/
abbrev PageTableEntriesApart (a len : Nat) : Prop :=
  (a + len ≤ 0x1000 ∨ 0x1008 ≤ a) ∧ (a + len ≤ 0x2000 ∨ 0x2020 ≤ a)

/-- Bytes apart from the page tables' frames `[0x1000, 0x3000)` are apart from the entries in
them. -/
theorem PageTableEntriesApart.of_frames {a len : Nat} (h : a + len ≤ 0x1000 ∨ 0x3000 ≤ a) :
    PageTableEntriesApart a len := by
  omega

/-- A part of bytes apart from the entries is apart from them. -/
theorem PageTableEntriesApart.sub {a len b n : Nat} (h : PageTableEntriesApart a len) (h₁ : a ≤ b)
    (h₂ : b + n ≤ a + len) : PageTableEntriesApart b n := by
  omega

/-- Bytes each apart from the entries are apart from them together: from a caller's bytewise
separation (`Prelude.MemoryRegion.Avoids`) to the interval a write guard states. -/
theorem PageTableEntriesApart.of_bytes {addr : BitVec 64} {len : Nat} (hpos : 0 < len)
    (hlow : addr.toNat + len ≤ 2^32)
    (h : ∀ i < len, PageTableEntriesApart (addr + BitVec.ofNat 64 i).toNat 1) :
    PageTableEntriesApart addr.toNat len := by
  have byte : ∀ i < len, PageTableEntriesApart (addr.toNat + i) 1 := fun i hi => by
    have h' := h i hi
    rwa [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (show addr.toNat + i < 2^64 by omega)] at h'
  -- an interval that meets an entry has its first byte there, or the entry's first byte
  have h₀ := byte 0 hpos
  have h₁ := byte (0x1000 - addr.toNat)
  have h₂ := byte (0x2000 - addr.toNat)
  omega

theorem physicalMemReadPTW_pml4e_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (h : IdentityPageTableMemory s.external) (la : BitVec 64) (pat : BitVec 3) :
    (Physical_Mem_Read_PTW la 0x1000 64 pat .PML4E).run s = (.ok 0x2027, s) := by
  have hr := physicalMemReadPTW64_run s hsmrr la 0x1000 pat .PML4E
    (fun i => UInt8.ofNat ((0x2027 : Nat) >>> (8 * i) % 256)) (by
      intro i hi
      simpa [BitVec.ofNat_add] using h.1 ⟨i, hi⟩)
  exact hr

theorem physicalMemReadPTW_pdpte_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (h : IdentityPageTableMemory s.external) (la : BitVec 64) (pat : BitVec 3) (page : Fin 4) :
    (Physical_Mem_Read_PTW la (BitVec.ofNat 64 (0x2000 + 8 * page.val)) 64 pat .PDPTE).run s =
      (.ok (BitVec.ofNat 64 (page.val <<< 30 ||| 0xe7)), s) := by
  have hr := physicalMemReadPTW64_run s hsmrr la (BitVec.ofNat 64 (0x2000 + 8 * page.val)) pat .PDPTE
    (fun i => UInt8.ofNat (((page.val <<< 30 ||| 0xe7) : Nat) >>> (8 * i) % 256)) (by
      intro i hi
      simpa [BitVec.ofNat_add] using h.2 page ⟨i, hi⟩)
  rw [hr]
  have hp : page = 0 ∨ page = 1 ∨ page = 2 ∨ page = 3 := by omega
  rcases hp with rfl | rfl | rfl | rfl <;> rfl


theorem checkProtectionKeyAccessViolation_run (s : RamState) (hcr4 : Prelude.SupportedIntegerCR4 s.CR4)
    (linear : Address_Translation) (access : Memory_Access_Type) (key : BitVec 4) :
    (Check_Protection_Key_Access_Violation linear access key true).run s = (.ok (), s) := by
  unfold Check_Protection_Key_Access_Violation
  split
  · rfl
  · dsimp only []
    have hpke : X86.CR4.PKE.run s = (.ok (0#1), s) := by
      simp [X86.CR4.PKE, x86_runtime, bind, pure, get, getThe, ExceptT.bind, ExceptT.pure,
        ExceptT.run, ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure, MonadStateOf.get,
        StateT.get, Functor.map, StateT.map, Bind.bind, ExceptT.lift, liftM, monadLift,
        MonadLift.monadLift, (supportedIntegerCR4_extractLsb_pke hcr4)]
    refine (specM_bind_run _ _ hpke).trans ?_
    repeat spec_bind_rfl!
    rfl

noncomputable def identityTranslation (linear : Address_Translation) : Translation where
  size_in_bytes := linear.num_bytes
  linear_address := linear.linear_address
  guest_physical_address := linear.linear_address
  physical_address := linear.linear_address
  is_write_allowed := true
  is_user_mode_address := true
  is_execute_disabled := false
  is_shadow_stack_address := false
  is_guest_physical_address_valid := false
  page_pat_pcd_pwt := 0
  memory_type := .Memory_Type_Unknown

theorem getMemoryType_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hmt : Prelude.WriteBackMemoryType instBindings s 0)
    (address : BitVec 64) (haddr : address.toNat < 2^32) :
    (Get_Memory_Type address 0).run s = (.ok .Memory_Type_Write_Back, s) :=
  (getMemoryType_readOnly address 0).run_of_result (hmt address haddr)

theorem checkAccessRightsPermission_run (s : RamState) (linear : Address_Translation)
    (access : Memory_Access_Type) (hcr4 : Prelude.SupportedIntegerCR4 s.CR4)
    (hshadow : linear.is_shadow_stack_access = false) :
    (Check_Access_Rights_Permission (identityTranslation linear) linear access).run s =
      (.ok (), s) := by
  by_cases hu : linear.translation_cpl = 3 ∧ linear.is_implicit_supervisor_mode_access = false <;>
    by_cases hnxe : s.IA32_EFER.NXE = 1#1 <;>
    simp [Check_Access_Rights_Permission, Check_User_Mode_Access_Permission,
      Check_Supervisor_Mode_Access_Permission, identityTranslation, Is_User_Mode_Access,
      Calculate_Page_Fault_Error_Code, X86.CR4.SMEP, X86.CR4.SMAP, cr4PAE_eq, X86.CR0.WP, Bit,
      Std.Boolean.To_Bit, Except.pure, Except.mapError, x86_runtime, get, getThe, liftM, bind,
      ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, MonadStateOf.get,
      monadLift, MonadLift.monadLift, pure, ExceptT.pure, StateT.pure, ExceptT.lift, Functor.map,
      Bind.bind, HOr.hOr, OrOp.or, strictOr, HAnd.hAnd, AndOp.and, strictAnd, hshadow, hu]
  all_goals
    cases access <;> by_cases hwp : s.CR0.extractLsb' 16 1 = 0#1 <;>
      simp_all [(supportedIntegerCR4_extractLsb_smep hcr4), (supportedIntegerCR4_extractLsb_smap hcr4), StateT.bind, StateT.map,
        StateT.get, StateT.pure, ExceptT.bindCont, pure, Pure.pure, Bind.bind]

/--
The permission check the page walk does before setting a dirty bit, for a writable user-mode
page and a non-shadow-stack write, with SMAP off: it passes, whatever the CPL and CR0.WP.
-/
theorem checkModeAccessPermission_run_of_write (s : RamState) (translation : Translation)
    (linear : Address_Translation) (access : Memory_Access_Type) (c : Prop) [Decidable c]
    (hcr4 : Prelude.SupportedIntegerCR4 s.CR4)
    (hshadow : linear.is_shadow_stack_access = false)
    (huser : translation.is_user_mode_address = true)
    (hwrite : translation.is_write_allowed = true)
    (haccess : access = .Memory_Write ∨ access = .Memory_Read_Modify_Write) :
    (if c then Check_User_Mode_Access_Permission translation linear access
      else Check_Supervisor_Mode_Access_Permission translation linear access).run s =
      (.ok true, s) := by
  rcases haccess with rfl | rfl <;> split <;>
    by_cases hwp : s.CR0.extractLsb' 16 1 = 0#1 <;>
    simp [Check_User_Mode_Access_Permission, Check_Supervisor_Mode_Access_Permission, X86.CR4.SMAP,
      X86.CR0.WP, get, getThe, liftM, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind,
      ExceptT.bindCont, MonadStateOf.get, monadLift, MonadLift.monadLift, pure, ExceptT.pure,
      StateT.pure, ExceptT.lift, Functor.map, Bind.bind, StateT.map, StateT.get, Pure.pure,
      x86_runtime, (supportedIntegerCR4_extractLsb_smap hcr4), hshadow, huser, hwrite, hwp] <;> rfl

theorem checkLASSViolation_run [X86.Machine.Bindings] (s : RamState) (linear : Address_Translation)
    (h : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LASS_Encoding false) :
    (Check_LASS_Violation linear).run s = (.ok (), s) := by
  have hc : (CPUID_LASS : X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok false, s) := by
    unfold CPUID_LASS
    exact readCPUIDFeature_run h
  unfold Check_LASS_Violation
  refine (specM_bind_run _ _ hc).trans ?_
  rfl

theorem reconstruct_identity_address (address : BitVec 64) (h : address.toNat < 2^32) :
    BitVec.ofNat 64 ((address.toNat / 2^30) * 2^30 +
      (BitVec.extractLsb' 0 30 address).toNat) = address := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_zero]
  have hm := Nat.mod_add_div address.toNat (2^30)
  omega

/-- `CPUID_CET_SS` returns what CPUID reports for CET_SS and leaves the state alone. -/
theorem cpuidCETSS_run [X86.Machine.Bindings] {s : RamState} {cet : Bool}
    (h : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding cet) :
    (CPUID_CET_SS : X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok cet, s) := by
  unfold CPUID_CET_SS
  exact readCPUIDFeature_run h

/--
The 4-level page walk on the identity map, for any access type: a linear address below 4 GiB
(a non-shadow-stack access) maps to itself through the 1 GiB page entry, and the state is
unchanged. For writes the walk's dirty-bit update is a no-op (`pageADBitUpdate_e7_run`).
-/
theorem translateWith4LevelPaging_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s) (hcr3 : s.CR3 = 0x1000)
    (hcr4 : Prelude.SupportedIntegerCR4 s.CR4)
    (hmax : Bindings.processor.config.Max_Physical_Address = 52) (hnxe : s.IA32_EFER.NXE = 0)
    (hearly : Bindings.processor.config.Feature_Early_Page_Access_Bit_Update = false)
    (hpt : IdentityPageTableMemory s.external)
    (hcet : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding b)
    (linear : Address_Translation) (access : Memory_Access_Type)
    (hshadow : linear.is_shadow_stack_access = false)
    (haddr : linear.linear_address.toNat < 2^32) :
    (Translate_With_4Level_Paging linear access false).run s =
      (.ok (identityTranslation linear), s) := by
  obtain ⟨cet, hcet⟩ := hcet
  have hcetRun := cpuidCETSS_run hcet
  have hguard : (X86.Runtime.guardedBool true (fun () => HLAT.Is_Address_Enabled linear.linear_address)).run s =
      (.ok ⟨false, fun _ => rfl⟩, s) := by
    unfold X86.Runtime.guardedBool
    simp only [dite_true]
    rw [specM_bind_run _ _ (hlatIsAddressEnabled_run s linear.linear_address)]
    rfl
  rw [Translate_With_4Level_Paging]
  refine (specM_bind_run _ _ hguard).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _ (s := s) rfl).trans ?_
  have hslice3 : (X86.Runtime.sliceInclusive s.CR3 51 12 : X86.Runtime.SpecM X86.Exception RamState (BitVec 40)).run s = (.ok 1, s) := by
    rw [hcr3]
    rfl
  refine (specM_bind_run _ _ hslice3).trans ?_
  refine (specM_bind_run (Std.Bits.Zero 12) _ (s := s) rfl).trans ?_
  have h47 : BitVec.extractLsb' 39 9 linear.linear_address = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat]
    have hz : linear.linear_address.toNat / 2^39 = 0 := Nat.div_eq_of_lt (by omega)
    simp [Nat.shiftRight_eq_div_pow, hz]
  have hslice47 : (X86.Runtime.sliceInclusive linear.linear_address 47 39 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 9)).run s = (.ok 0, s) := by
    change (Except.ok (BitVec.extractLsb' 39 9 linear.linear_address), s) = _
    rw [h47]
  refine (specM_bind_run _ _ hslice47).trans ?_
  refine (specM_bind_run (Std.Bits.Zero 3) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 9) (rightSize := 3) 0 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 40) (rightSize := 12) 1 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 12) (rightSize := 52) 0 0x1000) _ (s := s) rfl).trans ?_
  have hpcd : (X86.CR3.PCD : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 0, s) := by
    change (Except.ok (BitVec.extractLsb' 4 1 s.CR3), s) = _
    rw [hcr3]
    rfl
  have hpwt : (X86.CR3.PWT : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 0, s) := by
    change (Except.ok (BitVec.extractLsb' 3 1 s.CR3), s) = _
    rw [hcr3]
    rfl
  refine (specM_bind_run _ _ hpcd).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 1) (rightSize := 1) 0 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hpwt).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 2) (rightSize := 1) 0 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ (physicalMemReadPTW_pml4e_run s hsmrr hpt linear.linear_address 0)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Is_Zero (size := 1) (0 : BitVec 1))) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _ (s := s) rfl).trans ?_
  have hreadmax : (liftM (Config.Read.Max_Physical_Address (exception := X86.Exception)) :
      X86.Runtime.SpecM X86.Exception RamState Int).run s = (.ok 52, s) := by
    show (Config.Read.Max_Physical_Address, s) = _
    unfold Config.Read.Max_Physical_Address
    rw [show (Config.Value.Max_Physical_Address.value : Int) = 52 from hmax]
    rfl
  have hearlyv : (Config.Value.Feature_Early_Page_Access_Bit_Update.value : Bool) = false := hearly
  have hreadearly : (liftM (Config.Read.Feature_Early_Page_Access_Bit_Update (exception := X86.Exception)) :
      X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok false, s) := by
    show (Config.Read.Feature_Early_Page_Access_Bit_Update, s) = _
    unfold Config.Read.Feature_Early_Page_Access_Bit_Update
    rw [hearlyv]
    rfl
  refine (specM_bind_run _ _ hreadmax).trans ?_
  refine (specM_bind_run _ _ (value := true) (t := s) ?_).trans ?_
  · rw [specM_bind_run _ _ hreadmax]
    rfl
  rw [hnxe]
  refine (specM_bind_run _ _ hreadearly).trans ?_
  refine (specM_bind_run (Std.Bits.Zero 12) _ (s := s) rfl).trans ?_
  let page : Fin 4 := ⟨linear.linear_address.toNat / 2^30, by omega⟩
  have hindex : BitVec.extractLsb' 30 9 linear.linear_address = BitVec.ofNat 9 page.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rfl
  have hslice38 : (X86.Runtime.sliceInclusive linear.linear_address 38 30 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 9)).run s = (.ok (BitVec.ofNat 9 page.val), s) := by
    change (Except.ok (BitVec.extractLsb' 30 9 linear.linear_address), s) = _
    rw [hindex]
  refine (specM_bind_run _ _ hslice38).trans ?_
  refine (specM_bind_run (Std.Bits.Zero 3) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 9) (rightSize := 3) (BitVec.ofNat 9 page.val) 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 40) (rightSize := 12) 2 _) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 12) (rightSize := 52) 0 _) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 1) (rightSize := 1) 0 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.concatBits (leftSize := 2) (rightSize := 1) 0 0) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ (value := BitVec.ofNat 64 (page.val <<< 30 ||| 0xe7)) (t := s) ?_).trans ?_
  · have hp : page = 0 ∨ page = 1 ∨ page = 2 ∨ page = 3 := by omega
    rcases hp with hp | hp | hp | hp
    · rw [hp]; exact physicalMemReadPTW_pdpte_run s hsmrr hpt linear.linear_address 0 0
    · rw [hp]; exact physicalMemReadPTW_pdpte_run s hsmrr hpt linear.linear_address 0 1
    · rw [hp]; exact physicalMemReadPTW_pdpte_run s hsmrr hpt linear.linear_address 0 2
    · rw [hp]; exact physicalMemReadPTW_pdpte_run s hsmrr hpt linear.linear_address 0 3
  have hp : page = 0 ∨ page = 1 ∨ page = 2 ∨ page = 3 := by omega
  rcases hp with hp | hp | hp | hp
  all_goals rw [hp]
  all_goals
    refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _ (s := s) rfl).trans ?_
    refine (specM_bind_run _ _ hreadmax).trans ?_
    refine (specM_bind_run _ _ (value := true) (t := s) ?_).trans ?_
    · rw [specM_bind_run _ _ hreadmax]
      rfl
    rw [hnxe]
    cases access
    all_goals
      iterate 20
        spec_run [Check_Protection_Key_Access_Violation => checkProtectionKeyAccessViolation_run s hcr4 linear _ _,
          CPUID_CET_SS => hcetRun]
        try rw [hearlyv]
        try rw [hnxe]
      try
        refine (specM_bind_run _ _ (checkModeAccessPermission_run_of_write s _ linear _ _ hcr4 hshadow rfl rfl
          (by simp))).trans ?_
        iterate 5
          spec_run [Page_AD_Bit_Update => pageADBitUpdate_e7_run s _ _ _ _ _]
      have hpa := reconstruct_identity_address linear.linear_address haddr
      change BitVec.ofNat 64 (page.val * 2^30 +
        (BitVec.extractLsb' 0 30 linear.linear_address).toNat) = linear.linear_address at hpa
      rw [hp] at hpa
      exact congrArg (fun pa => (Except.ok ({identityTranslation linear with
        guest_physical_address := pa, physical_address := pa}), s)) hpa

noncomputable def writeBackIdentityTranslation (linear : Address_Translation) : Translation :=
  { identityTranslation linear with memory_type := .Memory_Type_Write_Back }

/--
`Translate` on the identity map, for any access type: identity translation with write-back
memory type, state unchanged.
-/
theorem translate_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hmt : Prelude.WriteBackMemoryType instBindings s 0)
    (hcr3 : s.CR3 = 0x1000) (hcr4 : Prelude.SupportedIntegerCR4 s.CR4)
    (hlme : s.IA32_EFER.LME = 1) (hmax : Bindings.processor.config.Max_Physical_Address = 52)
    (hnxe : s.IA32_EFER.NXE = 0)
    (hearly : Bindings.processor.config.Feature_Early_Page_Access_Bit_Update = false)
    (hpt : IdentityPageTableMemory s.external)
    (hcet : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding b)
    (linear : Address_Translation) (access : Memory_Access_Type)
    (hshadow : linear.is_shadow_stack_access = false)
    (haddr : linear.linear_address.toNat < 2^32) :
    (Translate linear access).run s = (.ok (writeBackIdentityTranslation linear), s) := by
  have hpae : (X86.CR4.PAE : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 1, s) := by
    rw [cr4PAE_run, supportedIntegerCR4_extractLsb_pae hcr4]
  have hla57 : (X86.CR4.LA57 : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run s = (.ok 0, s) := by
    change (Except.ok (BitVec.extractLsb' 12 1 s.CR4), s) = _
    simp only [(supportedIntegerCR4_extractLsb_la57 hcr4)]
  unfold Translate
  refine (specM_bind_run _ _ hpae).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _ (s := s) rfl).trans ?_
  rw [hlme]
  refine (specM_bind_run _ _ hla57).trans ?_
  refine (specM_bind_run _ _ (translateWith4LevelPaging_run s hsmrr hcr3 hcr4 hmax hnxe hearly hpt hcet linear access hshadow
    haddr)).trans ?_
  rw [hshadow]
  refine (specM_bind_run _ _ (checkAccessRightsPermission_run s linear access hcr4 hshadow)).trans ?_
  refine (specM_bind_run _ _ (isEPTEnabled_run s)).trans ?_
  refine (specM_bind_run _ _ (specM_liftNoSourceException_run _ _ _ _
    (getMemoryType_run s hmt linear.linear_address haddr))).trans ?_
  rfl

theorem physicalMemFetch_run [instBindings : X86.Machine.Bindings]
    (physical : Address_Translation) (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (byte : UInt8) (h : s.external.get? physical.translation1.physical_address = some byte) :
    (Physical_Mem_Fetch (σ := Ram) physical).run s = (.ok byte.toBitVec, s) := by
  unfold Physical_Mem_Fetch X86.__Physical_Mem_Fetch
  apply specM_liftNoSourceException_run
  change (do
    let result ← Bindings.PhysicalAccess.readPhysicalByte physical.translation1.physical_address
    pure result.toBitVec).run s = _
  rw [specM_bind_run _ _ (readPhysicalByte_run s hsmrr _ byte h)]
  rfl

end X86Proofs
