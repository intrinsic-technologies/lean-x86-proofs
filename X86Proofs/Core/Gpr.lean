import X86Proofs.Core.Mode

/-!
# General-purpose registers

Register numbers as lean-x86 forms them, how lean-x86's `Merge_GPR` stores a smaller result into a
64-bit register (`mergeGPR`), and what `Read_GPR` / `Write_GPR` do in 64-bit mode, at every
operand size they take (`readGPR_run`, `writeGPR_run`), with the 64-, 32- and 16-bit cases stated
directly: a 32-bit write zeroes the upper half of the register, a 16-bit (or 8-bit) write keeps
the bits above it. The 8-bit registers are read and written by other helpers (`Read_GPR8` /
`Write_GPR8`): `readGPR8_run_of_lowByte` / `writeGPR8_run_of_lowByte` for a low byte,
`readGPR8_run` / `writeGPR8_run` for any byte register, AH–BH (`HighByteReg`) included. The
accumulator forms read and write RAX through `RAX` / `Write_RAX` (`rax_run`, `writeRAX_run`).
Fixed-register helpers elsewhere (`RSI`, `Write_RCX`, …) go through `gprGet_eq` / `gprSet_eq`,
the register file read and write.
-/

namespace X86Proofs

open X86 X86.Helpers

/--
The 5-bit register number lean-x86 builds from the REX2 bit `hi4`, the REX bit `hi3` and the
3-bit ModRM/opcode field `low` (`concatBits (concatBits hi4 hi3) low`).
-/
def gprNumber (hi4 hi3 : BitVec 1) (low : BitVec 3) : BitVec 5 :=
  BitVec.ofNat 5 (((BitVec.ofNat 2 (hi4.toNat <<< 1 + hi3.toNat)).toNat <<< 3) + low.toNat)

/-- The slot of register number `r` in `State.GPR`. -/
def gprIndex (r : BitVec 5) : Fin 32 := ⟨r.toNat, r.isLt⟩

/-! ### lean-x86's register file

`GPR.get` and `GPR.set` are unfolded only here; other files rewrite with these. -/

/-- `GPR.get i` (in bounds) reads slot `i` of the register file. -/
theorem gprGet_eq {σ : Type} (i : Int) (h0 : 0 ≤ i) (h : i < 32) :
    (X86.GPR.get i : X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 64)) =
      (do let s ← getThe (X86.State σ); pure (s.GPR[i.toNat]'(by omega))) := by
  simp [X86.GPR.get, x86_runtime, h0, h]

/-- `GPR.set i v` (in bounds) writes `v` into slot `i` of the register file. -/
theorem gprSet_eq {σ : Type} (i : Int) (v : BitVec 64) (h0 : 0 ≤ i) (h : i < 32) :
    (X86.GPR.set i v : X86.Runtime.SpecM X86.Exception (X86.State σ) Unit) =
      modify (fun s : X86.State σ => { s with GPR := Vector.set s.GPR i.toNat v (by omega) }) := by
  simp only [X86.GPR.set, x86_runtime, h0, h, pure_bind]
  rfl

/-- In 64-bit mode, `Read_GPR` of register `index` is `GPR.get` of that slot, then a slice. -/
theorem readGPR_run_eq_get {σ : Type} (s : X86.State σ) (index : Fin 32)
    (N : Int) (hn : 0 ≤ N) (mode : In64BitMode s) :
    (Read_GPR (BitVec.ofNat 5 index.val) N).run s =
    (do
      X86.Runtime.assert (decide (N ≤ 64))
      let value ← X86.GPR.get (Int.ofNat index.val)
      X86.Runtime.CheckedSlice.read value 0 N :
        X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.Runtime.Bits N)).run s := by
  unfold Read_GPR
  simp only [hn, decide_true, x86_runtime, pure_bind]
  rw [specM_bind_run _ _ mode]
  finite_cases index <;> rfl

/-- In 64-bit mode, `Write_GPR` of register `index` is `GPR.get`, `Merge_GPR`, then `GPR.set`. -/
theorem writeGPR_run_eq_set {σ : Type} (s : X86.State σ) (index : Fin 32)
    (N : Int) (value : X86.Runtime.Bits N) (hn : 0 ≤ N) (mode : In64BitMode s) :
    (Write_GPR (BitVec.ofNat 5 index.val) value).run s =
    (do
      let old ← X86.GPR.get (Int.ofNat index.val)
      let result ← liftM (Merge_GPR value old)
      X86.GPR.set (Int.ofNat index.val) result :
        X86.Runtime.SpecM X86.Exception (X86.State σ) Unit).run s := by
  unfold Write_GPR
  simp only [hn, decide_true, x86_runtime, pure_bind]
  rw [specM_bind_run _ _ mode]
  finite_cases index <;> rfl

/--
How lean-x86's `Merge_GPR` stores an `n`-bit result into a 64-bit register: 32-bit results
zero the upper half, other sizes keep the bits above `n`.
-/
def mergeGPR (n : Nat) (v : BitVec n) (old : BitVec 64) : BitVec 64 :=
  if n = 32 then v.setWidth 64 else X86.Runtime.setSlice old 0 n v

theorem mergeGPR_64 (v old : BitVec 64) : mergeGPR 64 v old = v := by
  simp [mergeGPR, setSlice_full]

/-- A 32-bit result zero-extends into the register. -/
theorem mergeGPR_32 (v : BitVec 32) (old : BitVec 64) : mergeGPR 32 v old = v.setWidth 64 := rfl

/-- `Merge_GPR` at each size it accepts is `mergeGPR`. -/
theorem mergeGPR_run (N : Int) (hN : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64) (value : BitVec N.toNat)
    (old : BitVec 64) :
    Merge_GPR (size := N) value old = .ok (mergeGPR N.toNat value old) := by
  rcases hN with rfl | rfl | rfl | rfl <;>
  simp [Merge_GPR, mergeGPR, x86_runtime, bind, pure, Except.bind, Except.pure]

/-- lean-x86's `Merge_GPR` at 64 bits returns `mergeGPR`. -/
theorem mergeGPR64_run (value old : BitVec 64) :
    Merge_GPR (size := 64) value old = .ok (mergeGPR 64 value old) :=
  mergeGPR_run 64 (by decide) value old

/-- In 64-bit mode, `Read_GPR r 64` returns register `r` and leaves the state unchanged. -/
theorem readGPR64_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (mode : In64BitMode s) :
    (Read_GPR r 64).run s = (.ok s.GPR[gprIndex r], s) := by
  have h := readGPR_run_eq_get s (gprIndex r) 64 (by decide) mode
  simp only [gprIndex, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [h]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp [X86.GPR.get, x86_runtime, X86.Runtime.CheckedSlice.read, hindex]
  rfl

/-- In 64-bit mode, `Write_GPR r v` (64-bit `v`) sets register `r` to `v` and changes nothing else. -/
theorem writeGPR64_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (value : BitVec 64)
    (mode : In64BitMode s) :
    (Write_GPR (size := 64) r value).run s =
      (.ok (), { s with GPR := Vector.set s.GPR (gprIndex r) value }) := by
  have h := writeGPR_run_eq_set s (gprIndex r) 64 value (by decide) mode
  simp only [gprIndex, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [h]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, GPR.get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, x86_runtime, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, hindex, pure, ExceptT.pure, Int.toNat_natCast, Except.mapError,
    mergeGPR64_run, mergeGPR_64, GPR.set, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-! ### Other operand sizes -/

/--
In 64-bit mode, `Read_GPR r N` (`0 ≤ N ≤ 64`) returns the low `N` bits of register `r` and
leaves the state unchanged.
-/
theorem readGPR_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (N : Int) (h0 : 0 ≤ N) (h64 : N ≤ 64)
    (mode : In64BitMode s) :
    (Read_GPR r N).run s = (.ok (s.GPR[gprIndex r].setWidth N.toNat), s) := by
  have h := readGPR_run_eq_get s (gprIndex r) N h0 mode
  simp only [gprIndex, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [h, BitVec.setWidth_eq_extractLsb' (by omega)]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp [X86.GPR.get, x86_runtime, X86.Runtime.CheckedSlice.read, hindex, h64, h0]
  rfl

/--
In 64-bit mode, `Write_GPR r v` (`v` of 8, 16, 32 or 64 bits) sets register `r` to `v` merged
into its old value (`mergeGPR`) and changes nothing else.
-/
theorem writeGPR_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (N : Int)
    (hN : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64) (value : BitVec N.toNat) (mode : In64BitMode s) :
    (Write_GPR (size := N) r value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR N.toNat value s.GPR[gprIndex r]) }) := by
  have h := writeGPR_run_eq_set s (gprIndex r) N value (by omega) mode
  simp only [gprIndex, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [h]
  have hindex : (r.toNat : Int) < 32 := by have := r.isLt; omega
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, GPR.get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, x86_runtime, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, hindex, pure, ExceptT.pure, Int.toNat_natCast, Except.mapError,
    mergeGPR_run N hN, GPR.set, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- In 64-bit mode, `Read_GPR r 32` returns the low half of register `r`. -/
theorem readGPR32_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (mode : In64BitMode s) :
    (Read_GPR r 32).run s = (.ok (s.GPR[gprIndex r].setWidth 32), s) :=
  readGPR_run s r 32 (by decide) (by decide) mode

/--
In 64-bit mode, `Write_GPR r v` (32-bit `v`) sets register `r` to `v` zero-extended to 64 bits
(the upper half becomes zero) and changes nothing else.
-/
theorem writeGPR32_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (value : BitVec 32)
    (mode : In64BitMode s) :
    (Write_GPR (size := 32) r value).run s =
      (.ok (), { s with GPR := Vector.set s.GPR (gprIndex r) (value.setWidth 64) }) :=
  writeGPR_run s r 32 (by decide) value mode

/-- In 64-bit mode, `Read_GPR r 16` returns the low 16 bits of register `r`. -/
theorem readGPR16_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (mode : In64BitMode s) :
    (Read_GPR r 16).run s = (.ok (s.GPR[gprIndex r].setWidth 16), s) :=
  readGPR_run s r 16 (by decide) (by decide) mode

/--
In 64-bit mode, `Write_GPR r v` (16-bit `v`) replaces the low 16 bits of register `r` with `v`,
keeping the bits above, and changes nothing else.
-/
theorem writeGPR16_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (value : BitVec 16)
    (mode : In64BitMode s) :
    (Write_GPR (size := 16) r value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 16 value s.GPR[gprIndex r]) }) :=
  writeGPR_run s r 16 (by decide) value mode

/-! ### 8-bit registers with a REX prefix, and the accumulator -/

/--
In 64-bit mode, `Read_GPR8 r true` (an instruction with a REX-type prefix, so register numbers
4–7 are SPL, BPL, SIL, DIL rather than AH–BH) returns the low byte of register `r` and leaves the
state unchanged.
-/
theorem readGPR8_run_of_rex {σ : Type} (s : X86.State σ) (r : BitVec 5) (mode : In64BitMode s) :
    (Read_GPR8 r true).run s = (.ok (s.GPR[gprIndex r].setWidth 8), s) := by
  unfold Read_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> rfl

/-- In 64-bit mode, `Read_GPR8 r rex` for a register 0–3 (AL, CL, DL, BL, whatever the REX
flag) returns the low byte of register `r`. -/
theorem readGPR8_run_of_low {σ : Type} (s : X86.State σ) (r : BitVec 5) (hr : r.toNat < 4) (rex : Bool)
    (mode : In64BitMode s) :
    (Read_GPR8 r rex).run s = (.ok (s.GPR[gprIndex r].setWidth 8), s) := by
  unfold Read_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 4, r = BitVec.ofNat 5 i.val :=
    ⟨⟨r.toNat, hr⟩, by simp⟩
  clear hr
  finite_cases i <;> cases rex <;> rfl

/--
In 64-bit mode, `Read_GPR8 r rex` returns the low byte of register `r` whenever `r` names a low
byte: with a REX-type prefix (`rex = true`) any register, without one registers 0–3 (AL–BL;
4–7 would be AH–BH).
-/
theorem readGPR8_run_of_lowByte {σ : Type} (s : X86.State σ) (r : BitVec 5) (rex : Bool)
    (h : rex = true ∨ r.toNat < 4) (mode : In64BitMode s) :
    (Read_GPR8 r rex).run s = (.ok (s.GPR[gprIndex r].setWidth 8), s) :=
  h.elim (fun h => h ▸ readGPR8_run_of_rex s r mode) (fun h => readGPR8_run_of_low s r h rex mode)

/--
In 64-bit mode, `Write_GPR8 r true v` (an instruction with a REX-type prefix) replaces the low
byte of register `r` with `v`, keeping the bits above (`mergeGPR 8`), and changes nothing else.
-/
theorem writeGPR8_run_of_rex {σ : Type} (s : X86.State σ) (r : BitVec 5) (value : BitVec 8)
    (mode : In64BitMode s) :
    (Write_GPR8 r true value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r]) }) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> rfl

/-- In 64-bit mode, `Write_GPR8 r rex v` for a register 0–3 (AL, CL, DL, BL, whatever the REX
flag) replaces the low byte of register `r` with `v`. -/
theorem writeGPR8_run_of_low {σ : Type} (s : X86.State σ) (r : BitVec 5) (hr : r.toNat < 4)
    (rex : Bool) (value : BitVec 8) (mode : In64BitMode s) :
    (Write_GPR8 r rex value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r]) }) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 4, r = BitVec.ofNat 5 i.val :=
    ⟨⟨r.toNat, hr⟩, by simp⟩
  clear hr
  finite_cases i <;> cases rex <;> rfl

/-- In 64-bit mode, `Write_GPR8 r rex v` replaces the low byte of register `r` with `v` whenever
`r` names a low byte (as in `readGPR8_run_of_lowByte`). -/
theorem writeGPR8_run_of_lowByte {σ : Type} (s : X86.State σ) (r : BitVec 5) (rex : Bool)
    (h : rex = true ∨ r.toNat < 4) (value : BitVec 8) (mode : In64BitMode s) :
    (Write_GPR8 r rex value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r]) }) :=
  h.elim (fun h => h ▸ writeGPR8_run_of_rex s r value mode)
    (fun h => writeGPR8_run_of_low s r h rex value mode)

/-! ### 8-bit registers, AH–BH included -/

/--
lean-x86's `Read_GPR8 r rex` / `Write_GPR8 r rex` access bits 8–15 of a register rather than its
low byte: register numbers 4–7 without a REX-type prefix (`rex = false`) are AH, CH, DH, BH,
bits 8–15 of registers 0–3 (`r - 4`). Every other register number names the low byte of register
`r` (with a REX-type prefix, 4–7 are SPL, BPL, SIL, DIL).
-/
def HighByteReg (r : BitVec 5) (rex : Bool) : Prop := rex = false ∧ 4 ≤ r.toNat ∧ r.toNat < 8

instance (r : BitVec 5) (rex : Bool) : Decidable (HighByteReg r rex) := by
  unfold HighByteReg; infer_instance

/--
In 64-bit mode, `Read_GPR8 r rex` returns bits 8–15 of register `r - 4` for AH–BH
(`HighByteReg r rex`) and the low byte of register `r` otherwise, and leaves the state unchanged.
-/
theorem readGPR8_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (rex : Bool)
    (mode : In64BitMode s) :
    (Read_GPR8 r rex).run s =
      (.ok (if HighByteReg r rex then s.GPR[gprIndex (r - 4)].extractLsb' 8 8
        else s.GPR[gprIndex r].setWidth 8), s) := by
  unfold Read_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> cases rex <;> rfl

/--
In 64-bit mode, `Write_GPR8 r rex v` replaces bits 8–15 of register `r - 4` with `v` for AH–BH
(`HighByteReg r rex`) and the low byte of register `r` otherwise (`mergeGPR 8`), keeping the
other bits, and changes nothing else.
-/
theorem writeGPR8_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (rex : Bool) (value : BitVec 8)
    (mode : In64BitMode s) :
    (Write_GPR8 r rex value).run s =
      (.ok (), (if HighByteReg r rex then
        { s with
          GPR := Vector.set s.GPR (gprIndex (r - 4))
            (X86.Runtime.setSlice s.GPR[gprIndex (r - 4)] 8 8 value) }
      else
        { s with
          GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r]) })) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> cases rex <;> rfl

/-- The register holding the byte register an instruction without a REX-type prefix numbers `r`
(its 3-bit ModRM or opcode field): register `r` for AL, CL, DL, BL (0–3), register `r - 4` for
AH, CH, DH, BH (4–7). -/
def byteRegGpr (r : BitVec 3) : BitVec 5 := (r.setWidth 2).setWidth 5

/-- Register `byteRegGpr r`'s new value when no-REX byte register `r` is set to `v`: its low byte
(AL–BL, `mergeGPR 8`) or bits 8–15 (AH–BH) replaced, the other bits kept. -/
def mergeByteReg (r : BitVec 3) (v : BitVec 8) (old : BitVec 64) : BitVec 64 :=
  if r.toNat < 4 then mergeGPR 8 v old else X86.Runtime.setSlice old 8 8 v

section
open scoped X86.Runtime.Syntax

/--
The REX flag lean-x86's 8-bit register helpers get is `rex_prefix_present or rex2_prefix_present
or vex_prefix_present or evex_prefix_present`; it is set when there is a REX prefix.
-/
theorem lowByte_of_rex {a b c d : Bool} {p : Prop} (h : a = true ∨ p) :
    (a or b or c or d) = true ∨ p :=
  h.imp_left fun h => by subst h; cases b <;> cases c <;> cases d <;> rfl

/-- The REX flag lean-x86's 8-bit register helpers (`Read_GPR8`, `Write_GPR8`) get from an
instruction's context: a REX, REX2, VEX or EVEX prefix is present, so byte registers 4–7 are
SPL–DIL rather than AH–BH. -/
def byteRex (ctx : Instruction_Context) : Bool :=
  ctx.rex_prefix_present or ctx.rex2_prefix_present or ctx.vex_prefix_present or
    ctx.evex_prefix_present

end

/-- With no REX bits, register number `low` is `low`. -/
@[simp] theorem gprNumber_zero_toNat (low : BitVec 3) : (gprNumber 0 0 low).toNat = low.toNat := by
  revert low
  decide

/-- Without REX bits, a ModRM field below 4 names a register below 4 (AL–BL as a byte
register). -/
theorem gprNumber_zero_lt_four {low : BitVec 3} (h : low.toNat < 4) : (gprNumber 0 0 low).toNat < 4 := by
  rw [gprNumber_zero_toNat]
  exact h

/-- The low `N` bits (`0 ≤ N ≤ 64`) of a 64-bit value, as lean-x86's checked slice reads them. -/
theorem checkedSliceRead_zero_run {σ : Type} (s : X86.State σ) (x : BitVec 64) (N : Int) (h0 : 0 ≤ N)
    (h64 : N ≤ 64) :
    (X86.Runtime.CheckedSlice.read x 0 N :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.Runtime.Bits N)).run s =
      (.ok (x.setWidth N.toNat), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by omega)]
  simp [X86.Runtime.CheckedSlice.read, x86_runtime, h0, h64]

/-- `RAX` returns register 0. -/
theorem rax_run {σ : Type} (s : X86.State σ) :
    (RAX : Runtime.SpecM Exception (X86.State σ) (BitVec 64)).run s = (.ok s.GPR[gprIndex 0], s) := rfl

/--
`Write_RAX v` (`v` of 8, 16, 32 or 64 bits) sets register 0 to `v` merged into its old value
(`mergeGPR`), as `Write_GPR 0 v` does in 64-bit mode.
-/
theorem writeRAX_run {σ : Type} (s : X86.State σ) (N : Int)
    (hN : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64) (value : BitVec N.toNat) :
    (Write_RAX (size := N) value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 0) (mergeGPR N.toNat value s.GPR[gprIndex 0]) }) := by
  have h0 : (0 : Int) ≤ N := by omega
  simp only [Write_RAX, RAX_write, RAX, h0, decide_true, x86_runtime, ExceptT.run, bind,
    ExceptT.bind, ExceptT.mk, GPR.get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, Functor.map, pure, ExceptT.pure, Except.mapError,
    mergeGPR_run N hN, GPR.set, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- `writeRAX_run` for an operand size given as a natural number `n` (the form lean-x86's
operations take it in, `(n : Int)`). -/
theorem writeRAX_run_of_nat {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (value : BitVec n) :
    (Write_RAX (size := (n : Int)) value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 0) (mergeGPR n value s.GPR[gprIndex 0]) }) :=
  writeRAX_run s n (by omega) value

/--
`Write_RDX v` (`v` of 8, 16, 32 or 64 bits) sets register 2 to `v` merged into its old value
(`mergeGPR`), as `Write_GPR 2 v` does in 64-bit mode.
-/
theorem writeRDX_run {σ : Type} (s : X86.State σ) (N : Int)
    (hN : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64) (value : BitVec N.toNat) :
    (Write_RDX (size := N) value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 2) (mergeGPR N.toNat value s.GPR[gprIndex 2]) }) := by
  have h0 : (0 : Int) ≤ N := by omega
  simp only [Write_RDX, RDX_write, RDX, h0, decide_true, x86_runtime, ExceptT.run, bind,
    ExceptT.bind, ExceptT.mk, GPR.get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, Functor.map, pure, ExceptT.pure, Except.mapError,
    mergeGPR_run N hN, GPR.set, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- `writeRDX_run` for an operand size given as a natural number `n`. -/
theorem writeRDX_run_of_nat {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (value : BitVec n) :
    (Write_RDX (size := (n : Int)) value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 2) (mergeGPR n value s.GPR[gprIndex 2]) }) :=
  writeRDX_run s n (by omega) value

/--
`Write_RBX v` (`v` of 8, 16, 32 or 64 bits) sets register 3 to `v` merged into its old value
(`mergeGPR`), as `Write_GPR 3 v` does in 64-bit mode.
-/
theorem writeRBX_run {σ : Type} (s : X86.State σ) (N : Int)
    (hN : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64) (value : BitVec N.toNat) :
    (Write_RBX (size := N) value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 3) (mergeGPR N.toNat value s.GPR[gprIndex 3]) }) := by
  have h0 : (0 : Int) ≤ N := by omega
  simp only [Write_RBX, RBX_write, RBX, h0, decide_true, x86_runtime, ExceptT.run, bind,
    ExceptT.bind, ExceptT.mk, GPR.get, getThe, MonadStateOf.get, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, Functor.map, pure, ExceptT.pure, Except.mapError,
    mergeGPR_run N hN, GPR.set, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- The low `n` bits of `x` as lean-x86 slices them (`extractLsb' 0 n`) are `x.setWidth n`. -/
theorem extractLsb'_zero_eq_setWidth {w : Nat} (x : BitVec w) (n : Nat) (h : n ≤ w) :
    x.extractLsb' 0 n = x.setWidth n :=
  (BitVec.setWidth_eq_extractLsb' h).symm

/-- `AL` returns the low byte of register 0. -/
theorem al_run {σ : Type} (s : X86.State σ) :
    (AL : Runtime.SpecM Exception (X86.State σ) (BitVec 8)).run s =
      (.ok (s.GPR[gprIndex 0].setWidth 8), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [AL, X86.GPR.get, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `CL` returns the low byte of register 1 (the count of a shift or rotate by CL). -/
theorem cl_run {σ : Type} (s : X86.State σ) :
    (CL : Runtime.SpecM Exception (X86.State σ) (BitVec 8)).run s =
      (.ok (s.GPR[gprIndex 1].setWidth 8), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [CL, X86.GPR.get, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `AL_write v` replaces the low byte of register 0 with `v`, keeping the bits above
(`mergeGPR 8`), as `Write_RAX` at 8 bits does. -/
theorem alWrite_run {σ : Type} (s : X86.State σ) (value : BitVec 8) :
    (AL_write value : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 0) (mergeGPR 8 value s.GPR[gprIndex 0]) }) := by
  simp only [AL_write, x86_runtime, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, GPR.get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, pure,
    ExceptT.pure, GPR.set, modify, modifyGet, MonadStateOf.modifyGet, mergeGPR]
  rfl

/-! ### RDX:RAX

The fixed registers of the one-operand multiply and divide (`MUL`, `IMUL`, `DIV`, `IDIV`): RAX and
RDX read and written whole, their 32-bit halves `EAX` / `EDX` (a write zero-extends), their 16-bit
parts `AX` / `DX` (a write keeps the bits above), and `AH` (bits 8–15 of RAX). -/

/-- `RDX` returns register 2. -/
theorem rdx_run {σ : Type} (s : X86.State σ) :
    (RDX : Runtime.SpecM Exception (X86.State σ) (BitVec 64)).run s = (.ok s.GPR[gprIndex 2], s) := rfl

/-- `RBX` returns register 3 (CMPXCHG16B's RCX:RBX). -/
theorem rbx_run {σ : Type} (s : X86.State σ) :
    (RBX : Runtime.SpecM Exception (X86.State σ) (BitVec 64)).run s =
      (.ok s.GPR[gprIndex 3], s) := rfl

/-- `RCX` returns register 1, in any state type (`rcx_run`, `Program/ReadWrite/String.lean`, is
the same on `RamState` with `Operand.read`). -/
theorem rcx_gpr_run {σ : Type} (s : X86.State σ) :
    (RCX : Runtime.SpecM Exception (X86.State σ) (BitVec 64)).run s =
      (.ok s.GPR[gprIndex 1], s) := rfl

/-- `RAX_write v` sets register 0 to `v`. -/
theorem raxWrite_run {σ : Type} (s : X86.State σ) (v : BitVec 64) :
    (RAX_write v : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with GPR := Vector.set s.GPR (gprIndex 0) v }) := rfl

/-- `RDX_write v` sets register 2 to `v`. -/
theorem rdxWrite_run {σ : Type} (s : X86.State σ) (v : BitVec 64) :
    (RDX_write v : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with GPR := Vector.set s.GPR (gprIndex 2) v }) := rfl

/-- `liftM (Merge_GPR v old)` (`v` of 8, 16, 32 or 64 bits) returns `mergeGPR` and leaves the state
alone. -/
theorem liftM_mergeGPR_run {σ : Type} (s : X86.State σ) (N : Int)
    (hN : N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64) (value : BitVec N.toNat) (old : BitVec 64) :
    (liftM (Merge_GPR (size := N) value old) : Runtime.SpecM Exception (X86.State σ) (BitVec 64)).run
      s = (.ok (mergeGPR N.toNat value old), s) := by
  rw [mergeGPR_run N hN]
  rfl

/-- The low `n` bits of RAX, as lean-x86's multiplications read their multiplicand. -/
theorem raxLow_run {σ : Type} (s : X86.State σ) (n : Nat) (hn : n ≤ 64) :
    (do
      pure ()
      let r ← (RAX : Runtime.SpecM Exception (X86.State σ) (BitVec 64))
      pure (BitVec.extractLsb' 0 n r) : Runtime.SpecM Exception (X86.State σ) (BitVec n)).run s =
      (.ok (s.GPR[gprIndex 0].setWidth n), s) := by
  rw [BitVec.setWidth_eq_extractLsb' hn]
  rfl

/-- `AX` returns the low 16 bits of register 0. -/
theorem ax_run {σ : Type} (s : X86.State σ) :
    (AX : Runtime.SpecM Exception (X86.State σ) (BitVec 16)).run s =
      (.ok (s.GPR[gprIndex 0].setWidth 16), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [AX, X86.GPR.get, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `DX` returns the low 16 bits of register 2. -/
theorem dx_run {σ : Type} (s : X86.State σ) :
    (DX : Runtime.SpecM Exception (X86.State σ) (BitVec 16)).run s =
      (.ok (s.GPR[gprIndex 2].setWidth 16), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [DX, X86.GPR.get, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `EAX` returns the low 32 bits of register 0. -/
theorem eax_run {σ : Type} (s : X86.State σ) :
    (EAX : Runtime.SpecM Exception (X86.State σ) (BitVec 32)).run s =
      (.ok (s.GPR[gprIndex 0].setWidth 32), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [EAX, RAX, X86.GPR.get, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `EDX` returns the low 32 bits of register 2. -/
theorem edx_run {σ : Type} (s : X86.State σ) :
    (EDX : Runtime.SpecM Exception (X86.State σ) (BitVec 32)).run s =
      (.ok (s.GPR[gprIndex 2].setWidth 32), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [EDX, RDX, X86.GPR.get, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `ECX` returns the low 32 bits of register 1 (CMPXCHG8B's ECX:EBX). -/
theorem ecx_run {σ : Type} (s : X86.State σ) :
    (ECX : Runtime.SpecM Exception (X86.State σ) (BitVec 32)).run s =
      (.ok (s.GPR[gprIndex 1].setWidth 32), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [ECX, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `EBX` returns the low 32 bits of register 3 (CMPXCHG8B's ECX:EBX). -/
theorem ebx_run {σ : Type} (s : X86.State σ) :
    (EBX : Runtime.SpecM Exception (X86.State σ) (BitVec 32)).run s =
      (.ok (s.GPR[gprIndex 3].setWidth 32), s) := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [EBX, X86.Runtime.CheckedSlice.read, x86_runtime]
  rfl

/-- `AX_write v` replaces the low 16 bits of register 0 with `v` (`mergeGPR 16`). -/
theorem axWrite_run {σ : Type} (s : X86.State σ) (value : BitVec 16) :
    (AX_write value : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 0) (mergeGPR 16 value s.GPR[gprIndex 0]) }) := by
  simp only [AX_write, x86_runtime, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, GPR.get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, pure,
    ExceptT.pure, GPR.set, modify, modifyGet, MonadStateOf.modifyGet, mergeGPR]
  rfl

/-- `DX_write v` replaces the low 16 bits of register 2 with `v` (`mergeGPR 16`). -/
theorem dxWrite_run {σ : Type} (s : X86.State σ) (value : BitVec 16) :
    (DX_write value : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 2) (mergeGPR 16 value s.GPR[gprIndex 2]) }) := by
  simp only [DX_write, x86_runtime, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, GPR.get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, pure,
    ExceptT.pure, GPR.set, modify, modifyGet, MonadStateOf.modifyGet, mergeGPR]
  rfl

/-- `EAX_write v` sets register 0 to `v` zero-extended (`mergeGPR 32`). -/
theorem eaxWrite_run {σ : Type} (s : X86.State σ) (value : BitVec 32) :
    (EAX_write value : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 0) (mergeGPR 32 value s.GPR[gprIndex 0]) }) := by
  simp only [EAX_write, x86_runtime, mergeGPR_32]
  rfl

/-- `EDX_write v` sets register 2 to `v` zero-extended (`mergeGPR 32`). -/
theorem edxWrite_run {σ : Type} (s : X86.State σ) (value : BitVec 32) :
    (EDX_write value : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 2) (mergeGPR 32 value s.GPR[gprIndex 2]) }) := by
  simp only [EDX_write, x86_runtime, mergeGPR_32]
  rfl

/-- `AH_write v` replaces bits 8–15 of register 0 with `v`. -/
theorem ahWrite_run {σ : Type} (s : X86.State σ) (value : BitVec 8) :
    (AH_write value : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex 0) (X86.Runtime.setSlice s.GPR[gprIndex 0] 8 8 value) }) := by
  simp only [AH_write, x86_runtime, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, GPR.get, getThe,
    MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, pure,
    ExceptT.pure, GPR.set, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- AH then AL written: the low 16 bits replaced by `h ++ l` (`mergeGPR 16`), as one `AX` write. -/
theorem setSlice_ah_al (old : BitVec 64) (h l : BitVec 8) :
    X86.Runtime.setSlice (X86.Runtime.setSlice old 8 8 h) 0 8 l = mergeGPR 16 (h ++ l) old := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [mergeGPR, show (16 : Nat) ≠ 32 by decide, ite_false]
  rw [getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk]
  rw [BitVec.getLsbD_append]
  by_cases h8 : k < 8
  · simp [h8, show k < 16 by omega]
  · by_cases h16 : k < 16
    · simp [h8, h16, show 8 ≤ k by omega]
    · simp [h8, h16]

/-- Two writes of the same size to one register: the second replaces the first (`mergeGPR` keeps
or clears the same bits above `n` either way). -/
theorem mergeGPR_mergeGPR (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v w : BitVec n)
    (old : BitVec 64) : mergeGPR n w (mergeGPR n v old) = mergeGPR n w old := by
  rcases hn with rfl | rfl | rfl | rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [mergeGPR, show (8 : Nat) ≠ 32 by decide, ite_false]
    rw [getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk]
    split <;> simp_all
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [mergeGPR, show (16 : Nat) ≠ 32 by decide, ite_false]
    rw [getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk, getLsbD_setSlice _ _ _ _ _ hk]
    split <;> simp_all
  · simp only [mergeGPR_32]
  · simp only [mergeGPR_64]

/-- A register number without REX bits below 4 (AL–BL) from its 3-bit field below 4. -/
theorem gprNumber_low4 : ∀ r : BitVec 3, r.toNat < 4 → (gprNumber 0 0 r).toNat < 4 := by decide

/-- A register number without REX bits is its 3-bit field. -/
theorem gprNumber_zero_zero : ∀ r : BitVec 3, gprNumber 0 0 r = r.setWidth 5 := by decide

end X86Proofs
