import X86Proofs.Core.Run

/-!
# 64-bit mode and the flat code segment

`In64BitMode s` says lean-x86's `In_64Bit_Mode` returns `true` on `s` without changing it. It
depends only on CS and IA32_EFER.LMA, so it survives updates to every other field
(`In64BitMode.of_cs_lma_eq`).

This is the one file that unfolds lean-x86's `Is_64Bit_Code_Segment` and `Compute_Linear_Address`:
with long mode active, `userCodeSegment` (lean-x86's flat 64-bit user code segment) is a 64-bit
code segment, and in 64-bit mode the linear address of an offset in `userCodeSegment`, in the null
data segment `Mem_Fetch` builds from it, or in a flat data segment (`flatData`), is the offset
itself; through a 64-bit-mode segment with base `base` (FS or GS after a segment-override prefix)
it is `base + offset` (`computeLinearAddress_of_base`).

It is also the one file that unfolds lean-x86's mode bits read by several helpers: `CR0.PE`,
`CR0.PG`, `CR4.PAE`, `CR4.CET` and `RFLAGS.VM`. Each is a read of the current state's register
followed by a bit slice (`cr0PE_eq`, …); a proof unfolding a helper that reads them rewrites with
these and then uses the register facts it has (`Prelude.SupportedIntegerCR0`, …).
-/

namespace X86Proofs

open X86 X86.Helpers X86.UserProcess

/-! ### Mode bits -/

section ModeBits

variable {σ ε : Type}

/-- `CR0.PE` (protection enable) is bit 0 of CR0. -/
theorem cr0PE_eq :
    (X86.CR0.PE : X86.Runtime.SpecM ε (X86.State σ) X86.Runtime.Bit) =
      (do let s ← get; pure (s.CR0.extractLsb' 0 1)) := by
  simp [X86.CR0.PE, x86_runtime]

/-- `CR0.PG` (paging) is bit 31 of CR0. -/
theorem cr0PG_eq :
    (X86.CR0.PG : X86.Runtime.SpecM ε (X86.State σ) X86.Runtime.Bit) =
      (do let s ← get; pure (s.CR0.extractLsb' 31 1)) := by
  simp [X86.CR0.PG, x86_runtime]

/-- `CR4.PAE` (physical address extension) is bit 5 of CR4. -/
theorem cr4PAE_eq :
    (X86.CR4.PAE : X86.Runtime.SpecM X86.Exception (X86.State σ) X86.Runtime.Bit) =
      (do let s ← get; pure (s.CR4.extractLsb' 5 1)) := by
  simp [X86.CR4.PAE, x86_runtime]

/-- `CR4.CET` (control-flow enforcement) is bit 23 of CR4. -/
theorem cr4CET_eq :
    (X86.CR4.CET : X86.Runtime.SpecM X86.Exception (X86.State σ) X86.Runtime.Bit) =
      (do let s ← get; pure (s.CR4.extractLsb' 23 1)) := by
  simp [X86.CR4.CET, x86_runtime]

/-- `RFLAGS.VM` (virtual-8086 mode) is bit 17 of RFLAGS. -/
theorem rflagsVM_eq :
    (X86.RFLAGS.VM : X86.Runtime.SpecM X86.Exception (X86.State σ) X86.Runtime.Bit) =
      (do let s ← get; pure (s.RFLAGS.extractLsb' 17 1)) := by
  simp [X86.RFLAGS.VM, x86_runtime]

/-- Reading `CR0.PE` returns bit 0 of CR0 and leaves the state alone. -/
theorem cr0PE_run (s : X86.State σ) :
    (X86.CR0.PE : X86.Runtime.SpecM ε (X86.State σ) X86.Runtime.Bit).run s =
      (.ok (s.CR0.extractLsb' 0 1), s) := by
  rw [cr0PE_eq]; rfl

/-- Reading `CR0.PG` returns bit 31 of CR0 and leaves the state alone. -/
theorem cr0PG_run (s : X86.State σ) :
    (X86.CR0.PG : X86.Runtime.SpecM ε (X86.State σ) X86.Runtime.Bit).run s =
      (.ok (s.CR0.extractLsb' 31 1), s) := by
  rw [cr0PG_eq]; rfl

/-- Reading `CR4.PAE` returns bit 5 of CR4 and leaves the state alone. -/
theorem cr4PAE_run (s : X86.State σ) :
    (X86.CR4.PAE : X86.Runtime.SpecM X86.Exception (X86.State σ) X86.Runtime.Bit).run s =
      (.ok (s.CR4.extractLsb' 5 1), s) := by
  rw [cr4PAE_eq]; rfl

end ModeBits

/-- lean-x86's `In_64Bit_Mode` holds in `s`. -/
def In64BitMode {σ : Type} (s : X86.State σ) : Prop :=
  In_64Bit_Mode.run s = (.ok true, s)

/-- With long mode active, lean-x86's `Is_64Bit_Code_Segment` holds of the flat code segment. -/
theorem is64BitCodeSegment_userCodeSegment_run {σ : Type} (s : X86.State σ)
    (hlma : s.IA32_EFER.LMA = 1) :
    (Is_64Bit_Code_Segment userCodeSegment).run s = (.ok true, s) := by
  unfold Is_64Bit_Code_Segment
  change (Except.ok (s.IA32_EFER.LMA == (1 : BitVec 1) && true && true && true), s) = _
  rw [hlma]
  rfl

/-- The null data segment lean-x86's `Mem_Fetch` uses for a fetch through code segment
`segment`. -/
noncomputable def nullDataSegment (segment : X86.Helpers.Segment) : X86.Helpers.Segment :=
  { selector := 0, descriptor := X86.Runtime.InitializedBits.ofValue 0,
    descriptor_high := X86.Runtime.InitializedBits.ofValue 0, descriptor_valid := some false,
    is_stack := segment.is_stack, is_code := segment.is_code,
    is_64bit_mode_data_segment := segment.is_64bit_mode_data_segment }

/-- An offset in the flat code segment is its own linear address. -/
theorem computeLinearAddress_userCodeSegment_run {σ : Type} (s : X86.State σ) (offset : BitVec 64)
    (hlma : s.IA32_EFER.LMA = 1) :
    (Compute_Linear_Address userCodeSegment offset userCodeSegment).run s = (.ok offset, s) := by
  unfold Compute_Linear_Address
  rw [specM_bind_run _ _ (is64BitCodeSegment_userCodeSegment_run s hlma)]
  change (Except.ok (0#64 + offset), s) = _
  simp

/-- An offset in the null data segment of the flat code segment is its own linear address. -/
theorem computeLinearAddress_nullDataSegment_run {σ : Type} (s : X86.State σ)
    (offset : BitVec 64) (hlma : s.IA32_EFER.LMA = 1) :
    (Compute_Linear_Address (nullDataSegment userCodeSegment) offset userCodeSegment).run s =
      (.ok offset, s) := by
  unfold Compute_Linear_Address
  rw [specM_bind_run _ _ (is64BitCodeSegment_userCodeSegment_run s hlma)]
  change (Except.ok (0#64 + offset), s) = _
  simp

/--
The segment a flat 64-bit data access goes through: lean-x86's `Null_Segment` of `Prelude`'s
flat data segment (DS and ES, `isStack = false`) or stack segment (SS, `isStack = true`).
-/
noncomputable def flatData (isStack : Bool) : Segment := nullDataSegment {userStackSegment with is_stack := some isStack}

/-- An offset in a flat data segment is its own linear address. -/
theorem flatData_linear_address {σ : Type} (s : X86.State σ) (offset : BitVec 64) (isStack : Bool)
    (hlma : s.IA32_EFER.LMA = 1) :
    (Compute_Linear_Address (flatData isStack) offset userCodeSegment).run s = (.ok offset, s) := by
  unfold Compute_Linear_Address
  rw [specM_bind_run _ _ (is64BitCodeSegment_userCodeSegment_run s hlma)]
  cases isStack <;> (change (Except.ok (0#64 + offset), s) = _; simp)

/-- An offset in the flat stack segment itself (SS as loaded, not its null data segment; ENTER's
writability check goes through it) is its own linear address. -/
theorem computeLinearAddress_userStackSegment_run {σ : Type} (s : X86.State σ)
    (offset : BitVec 64) (hlma : s.IA32_EFER.LMA = 1) :
    (Compute_Linear_Address userStackSegment offset userCodeSegment).run s = (.ok offset, s) := by
  unfold Compute_Linear_Address
  rw [specM_bind_run _ _ (is64BitCodeSegment_userCodeSegment_run s hlma)]
  change (Except.ok (0#64 + offset), s) = _
  simp

/--
An offset in a 64-bit-mode data segment whose base is `base` (lean-x86's `Get_Segment_Base`), such
as FS or GS reached by a segment-override prefix: in 64-bit mode the linear address is
`base + offset`, wrapping at 2^64. `Is_System_Segment` must return (any answer): it is read first.
-/
theorem computeLinearAddress_of_base {σ : Type} (s : X86.State σ) (segment : Segment)
    (offset base : BitVec 64) (hlma : s.IA32_EFER.LMA = 1)
    (hmode : segment.is_64bit_mode_data_segment = some true) (b : Bool)
    (hsystem : Is_System_Segment segment = .ok b) (hbase : Get_Segment_Base segment = .ok base) :
    (Compute_Linear_Address segment offset userCodeSegment).run s = (.ok (base + offset), s) := by
  unfold Compute_Linear_Address
  rw [specM_bind_run _ _ (is64BitCodeSegment_userCodeSegment_run s hlma)]
  simp only [↓reduceIte, hmode, hsystem, hbase]
  cases b <;> rfl

/-- `In64BitMode` carries over to any state with the same CS and IA32_EFER.LMA. -/
theorem In64BitMode.of_cs_lma_eq {σ : Type} {s t : X86.State σ} (h : In64BitMode s)
    (hcs : t.CS = s.CS) (hlma : t.IA32_EFER.LMA = s.IA32_EFER.LMA) : In64BitMode t := by
  unfold In64BitMode In_64Bit_Mode Is_64Bit_Code_Segment at *
  simp only [bind, get, getThe, MonadStateOf.get, liftM, ExceptT.bind, ExceptT.run, ExceptT.mk,
    StateT.bind, ExceptT.bindCont, monadLift, MonadLift.monadLift, pure, ExceptT.pure, StateT.pure,
    StateT.get, ExceptT.lift, Functor.map, StateT.map,
    Segment_Descriptor.L.partial, Segment_Descriptor.D.partial, readSlice_specM] at *
  rw [hcs, hlma]
  revert h
  generalize Is_Code_Segment s.CS = c
  generalize (s.CS.descriptor.readSlice 53 1 : Except (X86.Runtime.Error X86.Exception) _) = r1
  generalize (s.CS.descriptor.readSlice 54 1 : Except (X86.Runtime.Error X86.Exception) _) = r2
  cases c <;> cases r1 <;> cases r2 <;>
    simp [Except.mapError, StateT.bind, StateT.pure, ExceptT.bindCont, bind, pure] <;>
    exact fun h => by injection h with h1; rw [h1]

/-- The flat 64-bit user code segment with long mode active is 64-bit mode. -/
theorem in64BitMode_of_userCodeSegment {σ : Type} {s : X86.State σ} (hcs : s.CS = userCodeSegment)
    (hlma : s.IA32_EFER.LMA = 1) : In64BitMode s := by
  unfold In64BitMode In_64Bit_Mode
  have hg : (get : X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.State σ)).run s = (.ok s, s) :=
    rfl
  rw [specM_bind_run _ _ hg, hcs]
  exact is64BitCodeSegment_userCodeSegment_run s hlma

end X86Proofs
