import X86Proofs.Step.Fetch

/-!
# Segment selectors (`Read_Segment`)

`MOV r/m, Sreg` (`8C /r`) reads the selector of the segment register its ModRM `reg` field names
through lean-x86's `Read_Segment`, which numbers them 0 ES, 1 CS, 2 SS, 3 DS, 4 FS, 5 GS (6 and 7
name none; the form raises #UD for them, `Is_Valid_Segment_Index`). `segSelector s r` is that
selector, `readSegment_run` is `Read_Segment` on `r`, and `isValidSegmentIndex_read` the form's
check. This file is the one that looks inside `Read_Segment` and `Is_Valid_Segment_Index`
(architecture rule 5).

The selectors are not components of an effect: no covered instruction writes a segment register, and
every step keeps them (they are part of `fixedPart`, `Program/Agrees.lean`). The triples that read
one (`MOV r/m, Sreg`, `PUSH FS`, `PUSH GS`) take its value as a parameter fixed by the precondition
(`segSelector s r = sel`, `s.FS.selector = sel`).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers

/-- The selector of segment register `r` in `Read_Segment`'s numbering: 0 ES, 1 CS, 2 SS, 3 DS, 4
FS, 5 GS; 0 for 6 and 7, which name no segment register. -/
def segSelector {σ : Type} (s : X86.State σ) (r : BitVec 3) : BitVec 16 :=
  match r.toNat with
  | 0 => s.ES.selector
  | 1 => s.CS.selector
  | 2 => s.SS.selector
  | 3 => s.DS.selector
  | 4 => s.FS.selector
  | 5 => s.GS.selector
  | _ => 0

/-- `Read_Segment` of segment register `r` (`r < 6`), the ModRM `reg` field as lean-x86's
`MOV r/m, Sreg` forms pass it, returns its selector and leaves the state alone. -/
theorem readSegment_run {σ : Type} (s : X86.State σ) (r : BitVec 3) (hr : r.toNat < 6) :
    (Read_Segment (σ := σ) r).run s = (.ok (segSelector s r), s) := by
  have h8 : ∀ r : BitVec 3, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
    decide
  rcases h8 r with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hr (by decide) | rfl

/-- A segment register number below 6 names a segment register `MOV r/m, Sreg` may read:
`Is_Valid_Segment_Index` for a read answers `true` (else the forms raise #UD). -/
theorem isValidSegmentIndex_read (r : BitVec 3) (hr : r.toNat < 6) :
    Is_Valid_Segment_Index r false = .ok true := by
  have h8 : ∀ r : BitVec 3, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by
    decide
  rcases h8 r with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hr (by decide) | rfl

/-- FS is segment register 4. -/
@[simp] theorem segSelector_fs {σ : Type} (s : X86.State σ) : segSelector s 4 = s.FS.selector := rfl

/-- GS is segment register 5. -/
@[simp] theorem segSelector_gs {σ : Type} (s : X86.State σ) : segSelector s 5 = s.GS.selector := rfl

/-- The fetches of a step keep the segment registers. -/
@[simp] theorem segSelector_afterFetches (s : RamState) (k : Nat) (r : BitVec 3) :
    segSelector (afterFetches s k) r = segSelector s r := rfl

/-- The start of a step keeps the segment registers. -/
@[simp] theorem segSelector_beforeFetch (s : RamState) (r : BitVec 3) :
    segSelector (beforeFetch s) r = segSelector s r := rfl

end X86Proofs
