import X86Proofs.Core.X87

/-!
# FNINIT specification

`FNINIT`: resets the x87 unit without checking for a pending exception: control word `037F`
(every exception masked, 64-bit precision, round to nearest), status word 0 (TOP 0), every tag
empty (`FFFF`), and the last instruction and data pointers and opcode 0.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The control word FNINIT leaves, field by field as lean-x86 sets it (`fninitControl_eq`: it is
`037F` whatever the old one). -/
def fninitControl (fcw : BitVec 16) : BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice
    (setSlice (setSlice fcw 0 1 1) 1 1 1) 2 1 1) 3 1 1) 4 1 1) 5 1 1) 6 2 1) 8 2 3) 10 2 0) 12 1 0)
    13 3 0

theorem fninitControl_eq (fcw : BitVec 16) : fninitControl fcw = 0x037F#16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [fninitControl, getElem_setSlice]

theorem fp87ControlSetSlice_run {σ : Type} (s : X86.State σ) (lo w : Int) (v : Bits w)
    (hlo : 0 ≤ lo) (hw : 0 ≤ w) (hle : lo + w ≤ 16) :
    (X86.FP87_Control.setSlice lo w v : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Control := setSlice s.FP87_Control lo.toNat w.toNat v }) := by
  unfold X86.FP87_Control.setSlice
  simp only [setSliceChecked_eq_pure _ _ hlo hw hle]
  rfl

theorem fninit_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FNINIT : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        FP87_Control := fninitControl s.FP87_Control
        FP87_Status := 0
        FP87_Tag_Word := 0xFFFF
        FP87_FDP := 0
        FP87_FIP := 0
        FP87_FCS := 0
        FP87_FDS := 0
        FP87_FOP := 0 }) := by
  unfold X86.Instructions.Operations.FNINIT
  spec_run [X86.FP87_Control.setSlice => fp87ControlSetSlice_run _ _ _ _ (by decide) (by decide)
    (by decide)]

end X86Proofs
