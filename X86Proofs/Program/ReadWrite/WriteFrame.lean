import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.ReadWrite.Store
import Prelude.Memory.Frame

/-!
# Memory frames

lean-x86's `Prelude.MemoryWriteFrame s t regions`: every byte outside the caller's permitted
`regions` is the same in `t` as in `s`. A program theorem states it of the whole run; here it
follows from the instructions' `AgreesExcept` frames (`AgreesExcept.memoryWriteFrame`) when their
memory components lie in the regions (`WritesWithin`), and composes along the run
(`memoryWriteFrame_trans`). Also: allocation and the direction flag through a frame (for a frame
without `.df`), and write permission (`MemWritable`) from bytewise allocation and separation from
the page tables (`PageTableEntriesApart.of_bytes` for a caller that keeps only their entries out).
-/

namespace X86Proofs

open X86 X86.Machine Prelude

/-- The memory components of an effect lie in the caller's permitted regions. -/
def WritesWithin (cs : List Component) (regions : Vector MemoryRegion n) : Prop :=
  ∀ c ∈ cs, ∀ address, c.Covers address →
    ∃ region ∈ regions, region.Contains address.toNat

/-- A frame whose memory components lie in `regions` changes no byte outside them. -/
theorem AgreesExcept.memoryWriteFrame {cs : List Component} {s t : RamState}
    {regions : Vector MemoryRegion n} (h : AgreesExcept cs s t)
    (hw : WritesWithin cs regions) : MemoryWriteFrame s t regions := by
  intro address hout
  apply h.byte
  intro c hc hcover
  obtain ⟨region, hr, hin⟩ := hw c hc address hcover
  exact hout region hr hin

/-- No step changes no byte. -/
theorem memoryWriteFrame_refl (s : RamState) (regions : Vector MemoryRegion n) :
    MemoryWriteFrame s s regions := fun _ _ => rfl

/-- Memory frames over the same regions compose. -/
theorem memoryWriteFrame_trans {s t u : RamState} {regions : Vector MemoryRegion n}
    (h₁ : MemoryWriteFrame s t regions) (h₂ : MemoryWriteFrame t u regions) :
    MemoryWriteFrame s u regions := fun a ha => (h₂ a ha).trans (h₁ a ha)

/-- A store keeps every allocated byte allocated. -/
theorem allocated_memStore {region : MemoryRegion} {m : Ram}
    (h : region.Allocated m) (address : BitVec 64) {n : Nat} (value : BitVec n) :
    region.Allocated (memStore m address value) := by
  intro a ha
  have hs : (m[a]?).isSome := Option.isSome_iff_exists.mpr (h a ha)
  exact Option.isSome_iff_exists.mp (memStore_isSome m address value a hs)

/-- A frame preserves allocation when its modified bytes are present in the result. -/
theorem AgreesExcept.allocated {cs : List Component} {s t : RamState} {region : MemoryRegion}
    (he : AgreesExcept cs s t) (h : region.Allocated s.external)
    (hm : ∀ a, (∃ c ∈ cs, c.Covers a) → (t.external[a]?).isSome) :
    region.Allocated t.external := by
  intro a ha
  by_cases hc : ∃ c ∈ cs, c.Covers a
  · exact Option.isSome_iff_exists.mp (hm a hc)
  · rw [he.byte (by intro c hc' hcov; exact hc ⟨c, hc', hcov⟩)]
    exact h a ha

/--
A byte of the page tables' frames `[0x1000, 0x3000)`, the PML4's at `0x1000` and the PDPT's at
`0x2000`. `Prelude.IdentityMappedMemory` fixes only the entries in them
(`PageTableEntriesApart`); this is the predicate of a caller that keeps both frames out of what it
writes.
-/
def PageTableReserved (address : BitVec 64) : Prop :=
  0x1000 ≤ address.toNat ∧ address.toNat < 0x3000

/-- Bytewise separation from the page tables' frames implies separation of the whole interval from
their entries. -/
theorem tables_of_not_reserved {addr : BitVec 64} {len : Nat}
    (hpos : 0 < len) (hlow : addr.toNat + len ≤ 2^32)
    (havoid : ∀ i < len, ¬ PageTableReserved (addr + BitVec.ofNat 64 i)) :
    PageTableEntriesApart addr.toNat len :=
  PageTableEntriesApart.of_bytes hpos hlow fun i hi => by
    have := havoid i hi
    unfold PageTableReserved at this
    omega

/-- Assemble write permission from bytewise allocation and separation. -/
theorem MemWritable.of_not_reserved {s : RamState} {addr : BitVec 64} {len : Nat}
    (hpos : 0 < len) (hlow : addr.toNat + len ≤ 2^32)
    (hmem : ∀ i < len, (s.external[addr + BitVec.ofNat 64 i]?).isSome)
    (havoid : ∀ i < len, ¬ PageTableReserved (addr + BitVec.ofNat 64 i)) :
    MemWritable s addr len :=
  ⟨hlow, hmem, tables_of_not_reserved hpos hlow havoid⟩

/-- Effects that do not write DF (`.df ∉ cs`: every effect but CLD's, STD's and POPF's) preserve
the direction flag used by string instructions. -/
theorem AgreesExcept.directionFlagClear {cs : List Component} {s t : RamState}
    (h : AgreesExcept cs s t) (hd : .df ∉ cs) (hs : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS) :
    Prelude.RFLAGS.DirectionFlagClear t.RFLAGS := by
  constructor
  change dfBit t.RFLAGS = 0
  rw [h.df hd]
  exact hs.df

end X86Proofs
