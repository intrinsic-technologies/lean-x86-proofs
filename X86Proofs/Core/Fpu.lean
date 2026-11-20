import X86Proofs.Core.Mode
import X86Proofs.Core.Lanes

/-!
# The x87 FPU state and the MMX registers

lean-x86 keeps the x87 FPU state as the eight *physical* 80-bit registers R0–R7 (`State.FP87`,
indexed by physical number, not relative to the stack top), the status word FSW
(`FP87_Status`: the exception flags IE…PE in bits 0–5, SF 6, ES 7, C0–C2 8–10, the stack top TOP
in bits 11–13, C3 14, B 15), the control word FCW (`FP87_Control`), the full tag word FTW
(`FP87_Tag_Word`, two bits per physical register: 00 valid, 01 zero, 10 special, 11 empty), and
the last-instruction pointers FIP, FCS, FDP, FDS and FOP.

MMX register `r` is the low 64 bits (the mantissa) of physical register R`r`: `Read_MMX r` reads
them (`readMMX_run`), `Write_MMX r v` sets R`r` to `0xFFFF ++ v` (sign and exponent all ones,
`mmxFpr`; `writeMMX_run`). Every MMX instruction also sets TOP to 0 (`FP87_Status.setTOP 0`,
`mmxStatus`; `fp87StatusSetTOP_run`) and the tag word to 0, all registers valid
(`FP87_Tag_Word.assign`, `fp87TagWordAssign_run`); EMMS sets the tag word to `0xFFFF` (all empty).
Before that, each checks for a pending unmasked x87 exception
(`FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions`), which does nothing when FSW.ES is
clear (`checkPending_run`, `fswES`).

The condition codes C0–C3 (FSW bits 8, 9, 10, 14, `fswCC` as a 4-bit value, bit `i` = C`i`) are
kept apart from the rest of the status word (`fswRest`, the word with them cleared): most x87
instructions leave some of them undefined (lean-x86 draws them from its oracle), so the library
treats them as their own component (`Component.fcc`, `Operand.fcc`). `fswMerge v old` is `v`'s
bits outside the codes with `old`'s codes (a write of the rest of the word), `fswSetCC fsw m v`
the codes selected by `m` replaced by `v`'s; `fsw_ext` splits an equation of status words.

This file is the one that unfolds lean-x86's `FP87.get`, `FP87.set`, `Read_MMX`, `Write_MMX`,
`FP87_Status.setTOP`, `FP87_Status.ES`, `FP87_Tag_Word.assign` and the pending-exception check.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The slot of physical x87 register (or MMX register) number `r` in `State.FP87`. -/
def fprIndex (r : BitVec 3) : Fin 8 := ⟨r.toNat, r.isLt⟩

/-- The 80-bit physical register an MMX write of `v` leaves (`Write_MMX`): sign and exponent all
ones, the mantissa `v`. -/
def mmxFpr (v : BitVec 64) : BitVec 80 := 0xFFFF#16 ++ v

/-- The status word after an MMX instruction: TOP (bits 11–13) set to 0, the other bits kept. -/
def mmxStatus (fsw : BitVec 16) : BitVec 16 := X86.Runtime.setSlice fsw 11 3 0#3

/-- The exception-summary bit ES (bit 7) of a status word. -/
def fswES (fsw : BitVec 16) : BitVec 1 := fsw.extractLsb' 7 1

/-- The condition codes C0, C1, C2, C3 of a status word (bits 8, 9, 10, 14) as a 4-bit value, bit
`i` being C`i`. -/
def fswCC (fsw : BitVec 16) : BitVec 4 := fsw.extractLsb' 14 1 ++ fsw.extractLsb' 8 3

/-- The status word without its condition codes: bits 8, 9, 10 and 14 cleared. -/
def fswRest (fsw : BitVec 16) : BitVec 16 := fsw &&& 0xB8FF#16

/-- Condition codes `c` placed at their status-word bits (C0–C2 at 8–10, C3 at 14), the rest 0. -/
def ccWord (c : BitVec 4) : BitVec 16 :=
  ((c.extractLsb' 3 1).setWidth 16 <<< 14) ||| ((c.extractLsb' 0 3).setWidth 16 <<< 8)

/-- The bits of `v` outside the condition codes, with the condition codes of `old`. -/
def fswMerge (v old : BitVec 16) : BitVec 16 := fswRest v ||| (old &&& 0x4700#16)

/-- `fsw` with the condition codes selected by mask `m` (bit `i`: C`i`) set to those of `v`. -/
def fswSetCC (fsw : BitVec 16) (m v : BitVec 4) : BitVec 16 :=
  fswRest fsw ||| ccWord ((fswCC fsw &&& ~~~m) ||| (v &&& m))

/-- The x87 last-instruction pointers as one value: FIP (bits 0–63), FCS (64–79), FDP (80–143),
FDS (144–159) and FOP (160–170). -/
def fpuPtrOf {σ : Type} (s : X86.State σ) : BitVec 171 :=
  s.FP87_FOP ++ s.FP87_FDS ++ s.FP87_FDP ++ s.FP87_FCS ++ s.FP87_FIP

/-- `s` with the last-instruction pointers set from a 171-bit value laid out as `fpuPtrOf`. -/
def setFpuPtr {σ : Type} (s : X86.State σ) (v : BitVec 171) : X86.State σ :=
  { s with
    FP87_FIP := v.extractLsb' 0 64
    FP87_FCS := v.extractLsb' 64 16
    FP87_FDP := v.extractLsb' 80 64
    FP87_FDS := v.extractLsb' 144 16
    FP87_FOP := v.extractLsb' 160 11 }

/-- The pointers read back after they are set. -/
@[simp] theorem fpuPtrOf_setFpuPtr {σ : Type} (s : X86.State σ) (v : BitVec 171) :
    fpuPtrOf (setFpuPtr s v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fpuPtrOf, setFpuPtr, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  repeat' split
  all_goals rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega)

/-- The low 64 bits of an MMX-written register are the value written. -/
@[simp] theorem mmxFpr_setWidth (v : BitVec 64) : (mmxFpr v).setWidth 64 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mmxFpr, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true,
    Bool.true_and, ite_true]

/-- The pending-exception summary of the status word after an MMX instruction is unchanged
(TOP is bits 11–13). -/
@[simp] theorem fswES_mmxStatus (fsw : BitVec 16) : fswES (mmxStatus fsw) = fswES fsw := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswES, mmxStatus, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp only [show ¬ (11 ≤ 7 + i ∧ 7 + i < 11 + 3) by omega, ite_false]

/-- `0xFFFF ++ v` as lean-x86's `concatBits` computes it. -/
theorem ofNat_eq_mmxFpr (v : BitVec 64) :
    BitVec.ofNat 80 (1208907372870555465154560 + v.toNat) = mmxFpr v := by
  rw [mmxFpr, ← ofNat_shiftLeft_add_eq_append_any]
  rfl

theorem lt16_cases {i : Nat} (hi : i < 16) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
    i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by
  omega

theorem lt4_cases {i : Nat} (hi : i < 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

/-- A status word is its condition codes and the rest. -/
theorem fsw_ext {f g : BitVec 16} (h1 : fswRest f = fswRest g) (h2 : fswCC f = fswCC g) :
    f = g := by
  have c := fun j => congrArg (fun x => x.getLsbD j) h2
  simp only [fswCC, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] at c
  have c0 := c 0
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  simp at c0 c1 c2 c3
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 := congrArg (·.getLsbD i) h1
  simp only [fswRest, BitVec.getLsbD_and] at e1
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp_all

@[simp] theorem fswCC_fswMerge (v old : BitVec 16) : fswCC (fswMerge v old) = fswCC old := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswCC, fswMerge, fswRest, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_and]
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;> simp

@[simp] theorem fswRest_fswMerge (v old : BitVec 16) : fswRest (fswMerge v old) = fswRest v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp [fswMerge, fswRest]

@[simp] theorem fswCC_fswSetCC (f : BitVec 16) (m v : BitVec 4) :
    fswCC (fswSetCC f m v) = (fswCC f &&& ~~~m) ||| (v &&& m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswCC, fswSetCC, fswRest, ccWord, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;> simp

@[simp] theorem fswRest_fswSetCC (f : BitVec 16) (m v : BitVec 4) :
    fswRest (fswSetCC f m v) = fswRest f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp [fswSetCC, fswRest, ccWord]

@[simp] theorem fswRest_fswRest (f : BitVec 16) : fswRest (fswRest f) = fswRest f := by
  simp only [fswRest, BitVec.and_assoc, BitVec.and_self]

/-- Setting TOP (bits 11–13) commutes with clearing the condition codes. -/
theorem fswRest_mmxStatus (f : BitVec 16) : fswRest (mmxStatus f) = mmxStatus (fswRest f) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswRest, mmxStatus, BitVec.getLsbD_and]
  rw [getLsbD_setSlice _ _ _ _ _ hi, getLsbD_setSlice _ _ _ _ _ hi, BitVec.getLsbD_and]
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp

/-- Setting TOP keeps the condition codes. -/
@[simp] theorem fswCC_mmxStatus (f : BitVec 16) : fswCC (mmxStatus f) = fswCC f := by
  have key : ∀ j, j < 16 → (j < 11 ∨ 14 ≤ j) → (mmxStatus f).getLsbD j = f.getLsbD j := by
    intro j hj hr
    simp only [mmxStatus]
    rw [getLsbD_setSlice _ _ _ _ _ hj]
    simp only [show ¬ (11 ≤ j ∧ j < 11 + 3) by omega, ite_false]
  have key' : ∀ j (hj : j < 16), (j < 11 ∨ 14 ≤ j) → (mmxStatus f)[j] = f[j] := by
    intro j hj hr
    simpa [BitVec.getLsbD_eq_getElem hj] using key j hj hr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswCC, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;>
    simp [key' 8 (by omega) (by omega), key' 9 (by omega) (by omega),
      key' 10 (by omega) (by omega), key' 14 (by omega) (by omega)]

/-- ES (bit 7) is outside the condition codes. -/
@[simp] theorem fswES_fswRest (f : BitVec 16) : fswES (fswRest f) = fswES f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp [fswES, fswRest]

/-! ### Run lemmas -/

section Run

variable {σ : Type}

/-- `Read_MMX r` reads the low 64 bits of physical register R`r` and changes nothing. -/
theorem readMMX_run (s : X86.State σ) (r : BitVec 3) :
    (Read_MMX r).run s = (.ok (s.FP87[fprIndex r].setWidth 64), s) := by
  have hr : (r.toNat : Int) < 8 := by have := r.isLt; omega
  simp [Read_MMX, X86.FP87.get, x86_runtime, hr, fprIndex,
    F80_Type.Mantissa]
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  rfl

/-- `Write_MMX r v` sets physical register R`r` to `0xFFFF ++ v` (`mmxFpr`) and changes nothing
else. -/
theorem writeMMX_run (s : X86.State σ) (r : BitVec 3) (v : BitVec 64) :
    (Write_MMX r v).run s =
      (.ok (), { s with FP87 := Vector.set s.FP87 (fprIndex r) (mmxFpr v) }) := by
  have hr : (r.toNat : Int) < 8 := by have := r.isLt; omega
  simp [Write_MMX, X86.FP87.set, x86_runtime, hr, fprIndex,
    ofNat_eq_mmxFpr]
  rfl

/-- `FP87_Status.setTOP 0` sets TOP to 0 (`mmxStatus`). -/
theorem fp87StatusSetTOP_run (s : X86.State σ) :
    (X86.FP87_Status.setTOP 0 : X86.Runtime.SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Status := mmxStatus s.FP87_Status }) := rfl

/-- `FP87_Tag_Word.assign v` sets the tag word to `v`. -/
theorem fp87TagWordAssign_run (s : X86.State σ) (v : BitVec 16) :
    (X86.FP87_Tag_Word.assign v : X86.Runtime.SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Tag_Word := v }) := rfl

/-- `FP87.get k` reads physical register R`r` (`k` its number) and changes nothing. -/
theorem fp87Get_run (s : X86.State σ) (k : Int) (r : BitVec 3) (hk : k = (r.toNat : Int)) :
    (X86.FP87.get k : X86.Runtime.SpecM X86.Exception (X86.State σ) _).run s =
      (.ok s.FP87[fprIndex r], s) := by
  subst hk
  have hr : (r.toNat : Int) < 8 := by have := r.isLt; omega
  simp [X86.FP87.get, x86_runtime, hr, fprIndex]
  rfl

/-- `FP87.set k v` sets physical register R`r` (`k` its number) to `v`. -/
theorem fp87Set_run (s : X86.State σ) (k : Int) (r : BitVec 3) (hk : k = (r.toNat : Int))
    (v : BitVec 80) :
    (X86.FP87.set k v : X86.Runtime.SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with FP87 := Vector.set s.FP87 (fprIndex r) v }) := by
  subst hk
  have hr : (r.toNat : Int) < 8 := by have := r.isLt; omega
  simp [X86.FP87.set, x86_runtime, hr, fprIndex]
  rfl

/-- The mantissa of an 80-bit value: its low 64 bits. -/
theorem f80Mantissa_eq (x : BitVec 80) : F80_Type.Mantissa x = x.extractLsb' 0 64 := by
  simp [F80_Type.Mantissa]

theorem fp87StatusES_run (s : X86.State σ) :
    (X86.FP87_Status.ES : X86.Runtime.SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (fswES s.FP87_Status), s) := by
  simp [X86.FP87_Status.ES, x86_runtime, fswES]
  rfl

/-- With FSW.ES clear (no pending unmasked x87 exception), the pending-exception check of the
MMX and waiting x87 instructions does nothing. -/
theorem checkPending_run [X86.Helpers.Unimplemented_Feature.Binding σ] (s : X86.State σ)
    (hes : fswES s.FP87_Status = 0) :
    (FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions :
        X86.Runtime.SpecM X86.Exception (X86.State σ) Unit).run s = (.ok (), s) := by
  simp only [fswES] at hes
  simp [FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions, X86.FP87_Status.ES,
    x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind, ExceptT.run, ExceptT.mk,
    StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift, ExceptT.pure,
    StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, hes]

end Run

end X86Proofs
