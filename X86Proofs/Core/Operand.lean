import X86Proofs.Core.Gpr
import X86Proofs.Core.Flags
import X86Proofs.Core.Oracle
import X86Proofs.Core.Xmm
import X86Proofs.Core.Fpu

/-!
# Operands, `read`, `writeOutputs` and `writeFlagsOutputs`

Shared by every instruction form: where an operand lives, how to read it from a state, and how
a form's outputs (destination value, flags, `Next_IP`) and the oracle bits it used are written
into the state (`writeOutputs`; `writeFlagsOutputs` for a form with no destination).

Memory operands (`Operand.mem`) are read and written through lean-x86's `PhysicalMemory`
interface, the same calls its physical-access bindings make, so they work for any memory model
`σ`; that a data access at a linear address reaches exactly these bytes is
`Step/Memory.lean`'s job. XMM registers (`Operand.xmm`, 128 bits) are the low halves of
lean-x86's ZMM registers (`Core/Xmm.lean`). `Operand.mxcsr` (32 bits) is the SSE control and status
register MXCSR, which the floating-point SSE forms read (rounding control, DAZ, FTZ, exception
masks) and write (the sticky exception flags), and LDMXCSR/STMXCSR load and store. `Operand.df` (1
bit) is the direction flag, RFLAGS bit 10 (`dfBit`), which CLD, STD and POPF write and the string
instructions read.

The x87 FPU state (`Core/Fpu.lean`): `Operand.fpr r` (80 bits) is physical register R`r`,
`Operand.mmx r` (64 bits) MMX register `r`, its low 64 bits, whose write sets R`r` to `0xFFFF ++ v`
(`mmxFpr`, as `Write_MMX` does); `Operand.fsw`, `Operand.ftw`, `Operand.fcw` (16 bits) are the
status, tag and control words, `Operand.fpuPtr` (171 bits) the last-instruction pointers FIP, FCS,
FDP, FDS and FOP (`fpuPtrOf`). The status word operand leaves out the condition codes C0–C3
(`fswRest`; a write keeps them); `Operand.fcc m` (4 bits) is the condition codes selected by the
mask `m`, which most x87 instructions leave partly undefined: an effect writes `Operand.fcc m`
with the codes it defines in `m`, and `Operand.fcc 0` (which reads and writes nothing) when it
defines none. The condition codes are the one operand an effect may not read
(`Operand.Visible`): the composition of effects (`Program/Compose.lean`) does not track their
undefined values.

Byte registers: `Operand.reg r : Operand 8` is the low byte of register `r` (AL–BL, and with a
REX-type prefix SPL–DIL, R8B–R15B); `Operand.regHigh r` is bits 8–15 of register `r` (AH, CH, DH,
BH for `r` = 0–3). `Operand.gpr8 r rex` is the one lean-x86's `Read_GPR8 r rex` / `Write_GPR8 r
rex` access (`readGPR8_run_gpr8`, `writeGPR8_run_gpr8`), and `Operand.byteReg r` the one an
instruction without a REX-type prefix names by its 3-bit field (0–3 AL–BL, 4–7 AH–BH). A write of
`Operand.byteReg r` is a 64-bit write of register `byteRegGpr r` with the byte merged in
(`mergeByteReg`, `writeOutputs_byteReg`), which is how instruction effects state it.
-/

namespace X86Proofs

open X86 X86.Machine

/-- Where an `n`-bit operand lives. -/
inductive Operand : Nat → Type where
  /-- The low `n` bits of general-purpose register number `r` (`n` ∈ {8, 16, 32, 64}; at 8 bits
  AL, CL, DL, BL, and with a REX prefix SPL, …, R15B). -/
  | reg {n : Nat} (r : BitVec 5) : Operand n
  /-- The `n / 8` bytes of memory at `addr`, `addr + 1`, …, little-endian (`n` ∈ {8, 16, 32,
  64}). The address is physical; on the identity map it is also the linear address. -/
  | mem {n : Nat} (addr : BitVec 64) : Operand n
  /-- XMM register number `r`: the low 128 bits of ZMM register `r` (`Core/Xmm.lean`), at
  `n = 128` (like `reg`, the size is not forced by the type, which keeps `match`es on operands
  free of index constraints). A write keeps bits 128–511, as a legacy SSE write does
  (`xmmMerge`). -/
  | xmm {n : Nat} (r : BitVec 5) : Operand n
  /-- Bits 8 to `8 + n - 1` of general-purpose register number `r`, at `n = 8`: AH, CH, DH, BH
  are `regHigh 0` to `regHigh 3` (byte registers 4–7 without a REX prefix, `Operand.gpr8`). A
  write keeps the other bits of the register. -/
  | regHigh {n : Nat} (r : BitVec 5) : Operand n
  /-- The SSE control and status register MXCSR (lean-x86's `State.MXCSR`), at `n = 32`: the
  exception flags (bits 0–5), DAZ (6), the exception masks (7–12), the rounding control RC
  (13–14), FTZ (15) and the reserved bits 16–31. A write replaces all of it. -/
  | mxcsr {n : Nat} : Operand n
  /-- The direction flag DF, RFLAGS bit 10 (`dfBit`), at `n = 1`. A write sets that bit only (to
  the low bit of the value), as lean-x86's `RFLAGS.setDF` does. -/
  | df {n : Nat} : Operand n
  /-- Physical x87 register R`r` (lean-x86's `State.FP87`, numbered physically, not relative to
  the stack top), at `n = 80`. A write replaces all 80 bits. -/
  | fpr {n : Nat} (r : BitVec 3) : Operand n
  /-- MMX register `r`: the low 64 bits (the mantissa) of physical register R`r`, at `n = 64`
  (`Read_MMX`). A write sets R`r` to `0xFFFF ++ v` (`mmxFpr`: sign and exponent all ones), as
  `Write_MMX` does, so it determines all 80 bits. -/
  | mmx {n : Nat} (r : BitVec 3) : Operand n
  /-- The x87 status word FSW (`State.FP87_Status`) without its condition codes, at `n = 16`: the
  exception flags (bits 0–5), SF (6), ES (7), TOP (11–13), B (15). A read gives the word with C0–C3
  (bits 8–10, 14) cleared (`fswRest`), a write sets the other bits and keeps C0–C3
  (`fswMerge`); the condition codes are `Operand.fcc`. -/
  | fsw {n : Nat} : Operand n
  /-- The x87 tag word FTW (`State.FP87_Tag_Word`), at `n = 16`: two bits per physical
  register. -/
  | ftw {n : Nat} : Operand n
  /-- The x87 control word FCW (`State.FP87_Control`), at `n = 16`. -/
  | fcw {n : Nat} : Operand n
  /-- The x87 last-instruction pointers FIP, FCS, FDP, FDS and FOP as one value (`fpuPtrOf`), at
  `n = 171`. A write replaces all five. -/
  | fpuPtr {n : Nat} : Operand n
  /-- The x87 condition codes C0–C3 (status-word bits 8, 9, 10, 14, `fswCC`) selected by the mask
  `m` (bit `i`: C`i`), at `n = 4`: a read gives the selected codes (the others 0), a write sets
  the selected codes to those of the value and keeps the others (`fswSetCC`). -/
  | fcc {n : Nat} (m : BitVec 4) : Operand n

/-- RAX (register number 0) as a 64-bit operand. -/
abbrev rax : Operand 64 := .reg 0

/-- RCX (register number 1) as a 64-bit operand. -/
abbrev rcx : Operand 64 := .reg 1

/-- RBX (register number 3) as a 64-bit operand. -/
abbrev rbx : Operand 64 := .reg 3

/-- RSI (register number 6) as a 64-bit operand. -/
abbrev rsi : Operand 64 := .reg 6

/-- RDI (register number 7) as a 64-bit operand. -/
abbrev rdi : Operand 64 := .reg 7

/-- The byte at physical address `addr`, or 0 where there is no RAM. -/
def memByte {σ : Type} [PhysicalMemory σ] (m : σ) (addr : BitVec 64) : UInt8 :=
  (PhysicalMemory.read m addr).getD 0

/--
The `n / 8` bytes at `addr`, `addr + 1`, … as an `n`-bit little-endian value, assembled the way
lean-x86's `readBytes` does.
-/
def memLoad {σ : Type} [PhysicalMemory σ] (m : σ) (addr : BitVec 64) (n : Nat) : BitVec n :=
  (List.range (n / 8)).foldl (fun acc i =>
    acc ||| (BitVec.ofNat n (memByte m (addr + BitVec.ofNat 64 i)).toNat <<< (8 * i))) 0

/--
`m` with the `n / 8` low bytes of `v` stored at `addr`, `addr + 1`, … (little-endian), one
`PhysicalMemory.write` per byte, as lean-x86's `writeBytes` does.
-/
def memStore {σ : Type} [PhysicalMemory σ] (m : σ) (addr : BitVec 64) {n : Nat} (v : BitVec n) :
    σ :=
  (List.range (n / 8)).foldl (fun m i =>
    PhysicalMemory.write m (addr + BitVec.ofNat 64 i) (UInt8.ofNat (v.toNat >>> (8 * i)))) m

/-- The value of operand `op` in `s`. -/
def Operand.read {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) : Operand n → BitVec n
  | .reg r => s.GPR[gprIndex r].setWidth n
  | .mem addr => memLoad s.external addr n
  | .xmm r => s.ZMM[xmmIndex r].setWidth n
  | .regHigh r => s.GPR[gprIndex r].extractLsb' 8 n
  | .mxcsr => s.MXCSR.setWidth n
  | .df => (dfBit s.RFLAGS).setWidth n
  | .fpr r => s.FP87[fprIndex r].setWidth n
  | .mmx r => s.FP87[fprIndex r].setWidth n
  | .fsw => (fswRest s.FP87_Status).setWidth n
  | .ftw => s.FP87_Tag_Word.setWidth n
  | .fcw => s.FP87_Control.setWidth n
  | .fpuPtr => (fpuPtrOf s).setWidth n
  | .fcc m => (fswCC s.FP87_Status &&& m).setWidth n

/-- `s` with operand `op` set to `v`. -/
def Operand.write {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) :
    Operand n → BitVec n → X86.State σ
  | .reg r, v => { s with GPR := Vector.set s.GPR (gprIndex r) (mergeGPR n v s.GPR[gprIndex r]) }
  | .mem addr, v => { s with external := memStore s.external addr v }
  | .xmm r, v =>
    { s with ZMM := Vector.set s.ZMM (xmmIndex r) (xmmMerge (v.setWidth 128) s.ZMM[xmmIndex r]) }
  | .regHigh r, v =>
    { s with
      GPR := Vector.set s.GPR (gprIndex r) (X86.Runtime.setSlice s.GPR[gprIndex r] 8 n v) }
  | .mxcsr, v => { s with MXCSR := v.setWidth 32 }
  | .df, v => { s with RFLAGS := X86.Runtime.setSlice s.RFLAGS 10 1 (v.setWidth 1) }
  | .fpr r, v => { s with FP87 := Vector.set s.FP87 (fprIndex r) (v.setWidth 80) }
  | .mmx r, v => { s with FP87 := Vector.set s.FP87 (fprIndex r) (mmxFpr (v.setWidth 64)) }
  | .fsw, v => { s with FP87_Status := fswMerge (v.setWidth 16) s.FP87_Status }
  | .ftw, v => { s with FP87_Tag_Word := v.setWidth 16 }
  | .fcw, v => { s with FP87_Control := v.setWidth 16 }
  | .fpuPtr, v =>
    { s with
      FP87_FIP := (v.setWidth 171).extractLsb' 0 64
      FP87_FCS := (v.setWidth 171).extractLsb' 64 16
      FP87_FDP := (v.setWidth 171).extractLsb' 80 64
      FP87_FDS := (v.setWidth 171).extractLsb' 144 16
      FP87_FOP := (v.setWidth 171).extractLsb' 160 11 }
  | .fcc m, v => { s with FP87_Status := fswSetCC s.FP87_Status m (v.setWidth 4) }

/-- Operand writes leave the repeat flag (`Repeat_String_Operation`) unchanged. -/
theorem Operand.write_repeat {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) (dst : Operand n) (v : BitVec n) :
    (dst.write s v).Repeat_String_Operation = s.Repeat_String_Operation := by
  cases dst <;> rfl

/--
The 8-bit register lean-x86's `Read_GPR8 r rex` and `Write_GPR8 r rex` access (`rex`: the
instruction has a REX-type prefix): AH, CH, DH, BH (`regHigh (r - 4)`) for register numbers 4–7
without one (`HighByteReg`), else the low byte of register `r`.
-/
def Operand.gpr8 (r : BitVec 5) (rex : Bool) : Operand 8 :=
  if HighByteReg r rex then .regHigh (r - 4) else .reg r

/--
A byte register as an instruction without a REX-type prefix numbers it, by its 3-bit ModRM or
opcode field `r`: 0–3 are AL, CL, DL, BL (the low bytes of registers 0–3), 4–7 are AH, CH, DH, BH
(bits 8–15 of registers 0–3). It lives in register `byteRegGpr r`.
-/
def Operand.byteReg (r : BitVec 3) : Operand 8 := Operand.gpr8 (gprNumber 0 0 r) false

/-- In 64-bit mode, `Read_GPR8 r rex` reads `Operand.gpr8 r rex`. -/
theorem readGPR8_run_gpr8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (rex : Bool) (mode : In64BitMode s) :
    (X86.Helpers.Read_GPR8 r rex).run s = (.ok ((Operand.gpr8 r rex).read s), s) := by
  rw [readGPR8_run s r rex mode, Operand.gpr8]
  split <;> rfl

/-- In 64-bit mode, `Write_GPR8 r rex v` writes `v` to `Operand.gpr8 r rex`. -/
theorem writeGPR8_run_gpr8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (rex : Bool) (value : BitVec 8) (mode : In64BitMode s) :
    (X86.Helpers.Write_GPR8 r rex value).run s = (.ok (), (Operand.gpr8 r rex).write s value) := by
  rw [writeGPR8_run s r rex value mode, Operand.gpr8]
  split <;> rfl

/-- A byte register that is not AH–BH (a REX-type prefix, or registers 0–3) is a low byte. -/
theorem Operand.gpr8_of_lowByte {r : BitVec 5} {rex : Bool} (h : rex = true ∨ r.toNat < 4) :
    Operand.gpr8 r rex = .reg r := by
  unfold Operand.gpr8
  split
  · rename_i hh
    obtain ⟨h1, h2, -⟩ := hh
    rcases h with h | h
    · rw [h1] at h; cases h
    · omega
  · rfl

/-- No-REX byte register `r` as a register operand: the low byte (`r < 4`) or bits 8–15 of
register `byteRegGpr r`. -/
theorem Operand.byteReg_eq (r : BitVec 3) :
    Operand.byteReg r =
      if r.toNat < 4 then .reg (byteRegGpr r) else .regHigh (byteRegGpr r) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 8, r = BitVec.ofNat 3 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> rfl

/-- The value of no-REX byte register `r`: the low byte or bits 8–15 of register
`byteRegGpr r`. -/
theorem Operand.read_byteReg {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3) :
    (Operand.byteReg r).read s =
      if r.toNat < 4 then s.GPR[gprIndex (byteRegGpr r)].setWidth 8
      else s.GPR[gprIndex (byteRegGpr r)].extractLsb' 8 8 := by
  rw [Operand.byteReg_eq]
  split <;> rfl

/-- Writing no-REX byte register `r` sets register `byteRegGpr r` to its old value with that
byte replaced (`mergeByteReg`). -/
theorem Operand.write_byteReg {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3)
    (v : BitVec 8) :
    (Operand.byteReg r).write s v =
      { s with
        GPR := Vector.set s.GPR (gprIndex (byteRegGpr r))
          (mergeByteReg r v s.GPR[gprIndex (byteRegGpr r)]) } := by
  rw [Operand.byteReg_eq, mergeByteReg]
  split <;> rfl

/-- `s` with `Next_IP` set and nothing else changed: the form-level result of an instruction that
only moves on (NOP). -/
def withNextIP {σ : Type} (s : X86.State σ) (nextIP : BitVec 64) : X86.State σ :=
  { s with Next_IP := nextIP }

/--
The outputs of an instruction with one destination and status flags: `s` with
`Next_IP` set (RIP itself is advanced later, by `step`), `oracleUsed` oracle bits used up, the
flags `out.2` stored and the destination `dst` set to `out.1`. Everything else is unchanged.
-/
def writeOutputs {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) (dst : Operand n) (out : BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) : X86.State σ :=
  dst.write (setFlags { s with Next_IP := nextIP, oracle := oracleSkip s.oracle oracleUsed } out.2)
    out.1

/--
Form-level write-back for an instruction that only sets the status flags (CMP, TEST): `s` with
`Next_IP` set, `oracleUsed` oracle bits used up and the flags `f` stored. It is `writeOutputs`
without the destination write; registers and memory are unchanged.
-/
def writeFlagsOutputs {σ : Type} (s : X86.State σ) (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    X86.State σ :=
  setFlags { s with Next_IP := nextIP, oracle := oracleSkip s.oracle oracleUsed } f

@[simp] theorem Operand.read_reg64 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) :
    (Operand.reg r : Operand 64).read s = s.GPR[gprIndex r] := by
  simp [Operand.read]

@[simp] theorem Operand.write_reg64 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) (v : BitVec 64) :
    (Operand.reg r : Operand 64).write s v = { s with GPR := Vector.set s.GPR (gprIndex r) v } := by
  simp [Operand.write, mergeGPR_64]

@[simp] theorem Operand.read_reg32 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) :
    (Operand.reg r : Operand 32).read s = s.GPR[gprIndex r].setWidth 32 := rfl

/-- Writing a 32-bit register sets the whole 64-bit register to the zero-extended value. -/
@[simp] theorem Operand.write_reg32 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) (v : BitVec 32) :
    (Operand.reg r : Operand 32).write s v =
      { s with GPR := Vector.set s.GPR (gprIndex r) (v.setWidth 64) } := rfl

@[simp] theorem Operand.read_reg16 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) :
    (Operand.reg r : Operand 16).read s = s.GPR[gprIndex r].setWidth 16 := rfl

/-- Writing a 16-bit register replaces its low 16 bits and keeps the bits above. -/
@[simp] theorem Operand.write_reg16 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (v : BitVec 16) :
    (Operand.reg r : Operand 16).write s v =
      { s with GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 16 v s.GPR[gprIndex r]) } := rfl

/-- An 8-bit register operand is the low byte of the register (with a REX prefix, or for
registers 0–3; AH–BH are not register operands). -/
@[simp] theorem Operand.read_reg8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) :
    (Operand.reg r : Operand 8).read s = s.GPR[gprIndex r].setWidth 8 := rfl

/-- Writing an 8-bit register replaces its low byte and keeps the bits above. -/
@[simp] theorem Operand.write_reg8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (v : BitVec 8) :
    (Operand.reg r : Operand 8).write s v =
      { s with GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 v s.GPR[gprIndex r]) } := rfl

/-- AH–BH: bits 8–15 of register `r`. -/
@[simp] theorem Operand.read_regHigh8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) :
    (Operand.regHigh r : Operand 8).read s = s.GPR[gprIndex r].extractLsb' 8 8 := rfl

/-- Writing AH–BH replaces bits 8–15 of the register and keeps the others. -/
@[simp] theorem Operand.write_regHigh8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (v : BitVec 8) :
    (Operand.regHigh r : Operand 8).write s v =
      { s with
        GPR := Vector.set s.GPR (gprIndex r) (X86.Runtime.setSlice s.GPR[gprIndex r] 8 8 v) } :=
  rfl

/-- A register write is `Vector.set` of the merged value (`mergeGPR`), the form lean-x86's fixed
register writes (`RAX_write`, `AX_write`, …) take. -/
theorem Operand.write_reg_eq_set {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (r : BitVec 5) (v : BitVec n) :
    (Operand.reg r : Operand n).write s v =
      { s with GPR := Vector.set s.GPR (gprIndex r) (mergeGPR n v s.GPR[gprIndex r]) } := rfl

/-- Bits 8–15 of a register replaced by `h` (lean-x86's `AH_write` on RAX), then its low byte by
`l` (`AL_write`): the low 16 bits replaced by `h ++ l`. -/
theorem Operand.write_reg8_setSlice_high {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (h l : BitVec 8) :
    (Operand.reg r : Operand 8).write
        { s with GPR := Vector.set s.GPR (gprIndex r) (X86.Runtime.setSlice s.GPR[gprIndex r] 8 8 h) }
        l =
      (Operand.reg r : Operand 16).write s (h ++ l) := by
  simp only [Operand.write, Vector.set_set, ← setSlice_ah_al]
  simp [mergeGPR]

/-- A no-REX byte register write is a 64-bit write of register `byteRegGpr r` (`mergeByteReg`). -/
theorem Operand.write_byteReg_eq_reg64 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 3) (v : BitVec 8) :
    (Operand.byteReg r).write s v =
      (Operand.reg (byteRegGpr r) : Operand 64).write s
        (mergeByteReg r v ((Operand.reg (byteRegGpr r) : Operand 64).read s)) := by
  rw [Operand.write_byteReg, Operand.write_reg64, Operand.read_reg64]

/-- A register operand sees only the general-purpose registers. -/
theorem Operand.read_reg_of_gpr_eq {σ τ : Type} [PhysicalMemory σ] [PhysicalMemory τ] {n : Nat}
    {s : X86.State σ} {t : X86.State τ} (h : s.GPR = t.GPR) (r : BitVec 5) :
    (Operand.reg r : Operand n).read s = (Operand.reg r : Operand n).read t := by
  simp [Operand.read, h]

/-- `Operand.read` sees only the general-purpose registers, the vector registers, MXCSR, the
direction flag, the x87 state and memory. -/
theorem Operand.read_of_eq {σ : Type} [PhysicalMemory σ] {n : Nat} {s t : X86.State σ}
    (hg : s.GPR = t.GPR) (hz : s.ZMM = t.ZMM) (he : s.external = t.external)
    (hm : s.MXCSR = t.MXCSR) (hd : dfBit s.RFLAGS = dfBit t.RFLAGS) (hf : s.FP87 = t.FP87)
    (hfs : s.FP87_Status = t.FP87_Status) (hft : s.FP87_Tag_Word = t.FP87_Tag_Word)
    (hfc : s.FP87_Control = t.FP87_Control) (hp : fpuPtrOf s = fpuPtrOf t) (op : Operand n) :
    op.read s = op.read t := by
  cases op <;> simp [Operand.read, hg, he, hz, hm, hd, hf, hfs, hft, hfc, hp]

/-- Writing memory leaves the registers alone. -/
@[simp] theorem Operand.read_reg_write_mem {σ : Type} [PhysicalMemory σ] {n m : Nat}
    (s : X86.State σ) (r : BitVec 5) (addr : BitVec 64) (v : BitVec n) :
    (Operand.reg r : Operand m).read ((Operand.mem addr : Operand n).write s v) =
      (Operand.reg r : Operand m).read s := rfl

/-- Writing a register leaves the other registers alone. -/
theorem Operand.read_write_reg_of_ne {σ : Type} [PhysicalMemory σ] {n m : Nat} (s : X86.State σ)
    {r r' : BitVec 5} (hne : r ≠ r') (v : BitVec n) :
    (Operand.reg r' : Operand m).read ((Operand.reg r : Operand n).write s v) =
      (Operand.reg r' : Operand m).read s := by
  have hi : gprIndex r ≠ gprIndex r' := fun h => hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp h))
  simp [Operand.write, Operand.read, Fin.val_ne_of_ne hi]

/-- `writeOutputs` to a register leaves memory unchanged. -/
@[simp] theorem writeOutputs_reg_external {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ) (r : BitVec 5)
    (out : BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (writeOutputs s (.reg r) out oracleUsed nextIP).external = s.external := rfl

/-- After a 64-bit `writeOutputs` to register `r`, reading `r` gives the written value. -/
@[simp] theorem Operand.read_writeOutputs_self {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (out : BitVec 64 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeOutputs s (.reg r) out oracleUsed nextIP) = out.1 := by
  simp [writeOutputs, setFlags]

/--
After a 32-bit `writeOutputs` to register `r`, the full 64-bit register `r` is the written value
zero-extended: the upper half is zero.
-/
@[simp] theorem Operand.read_writeOutputs_self32 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (out : BitVec 32 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeOutputs s (.reg r : Operand 32) out oracleUsed nextIP) =
      out.1.setWidth 64 := by
  simp [writeOutputs, setFlags]

/--
After an `n`-bit `writeOutputs` to register `r`, the full 64-bit register `r` is the written value
merged into its old value (`mergeGPR`: the low `n` bits replaced; at 32 bits, zero-extended).
-/
theorem Operand.read_writeOutputs_self_merge {σ : Type} [PhysicalMemory σ] {n : Nat}
    (s : X86.State σ) (r : BitVec 5) (out : BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeOutputs s (.reg r : Operand n) out oracleUsed nextIP) =
      mergeGPR n out.1 ((Operand.reg r : Operand 64).read s) := by
  simp [writeOutputs, setFlags, Operand.write]

/--
After a `writeOutputs` (of any size) to register `r`, a register with a different 5-bit number
reads as before (at any size).
-/
theorem Operand.read_writeOutputs_of_ne {σ : Type} [PhysicalMemory σ] {n m : Nat} (s : X86.State σ) {r r' : BitVec 5}
    (hne : r ≠ r') (out : BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r' : Operand m).read (writeOutputs s (.reg r) out oracleUsed nextIP) =
      (Operand.reg r' : Operand m).read s := by
  have hi : gprIndex r ≠ gprIndex r' := fun h => hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp h))
  simp [writeOutputs, setFlags, Operand.write, Operand.read, Fin.val_ne_of_ne hi]

/-- `writeOutputs` to no-REX byte register `r` is `writeOutputs` of register `byteRegGpr r` at 64
bits, with the byte merged into its old value (`mergeByteReg`). -/
theorem writeOutputs_byteReg {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3)
    (out : BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    writeOutputs s (Operand.byteReg r) out oracleUsed nextIP =
      writeOutputs s (Operand.reg (byteRegGpr r) : Operand 64)
        (mergeByteReg r out.1 ((Operand.reg (byteRegGpr r) : Operand 64).read s), out.2)
        oracleUsed nextIP := by
  simp only [writeOutputs, Operand.write_byteReg_eq_reg64]
  rfl

/-- A 128-bit XMM operand is the low 128 bits of the ZMM register. -/
@[simp] theorem Operand.read_xmm {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5) :
    (Operand.xmm r : Operand 128).read s = s.ZMM[xmmIndex r].setWidth 128 := rfl

/-- A 128-bit XMM write replaces the low 128 bits of the ZMM register. -/
@[simp] theorem Operand.write_xmm {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (v : BitVec 128) :
    (Operand.xmm r : Operand 128).write s v =
      { s with ZMM := Vector.set s.ZMM (xmmIndex r) (xmmMerge v s.ZMM[xmmIndex r]) } := by
  simp [Operand.write]

/-- After an XMM write, the register reads the value written. -/
@[simp] theorem Operand.read_write_xmm_self {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (v : BitVec 128) :
    (Operand.xmm r : Operand 128).read ((Operand.xmm r : Operand 128).write s v) = v := by
  simp [Operand.read, Operand.write]

/-- An XMM write leaves the other XMM registers alone. -/
theorem Operand.read_write_xmm_of_ne {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    {r r' : BitVec 5} (hne : r ≠ r') (v : BitVec 128) :
    (Operand.xmm r' : Operand 128).read ((Operand.xmm r : Operand 128).write s v) =
      (Operand.xmm r' : Operand 128).read s := by
  have hi : xmmIndex r ≠ xmmIndex r' := fun h => hne (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp h))
  simp [Operand.write, Operand.read, Fin.val_ne_of_ne hi]

/-- An XMM write leaves the general-purpose registers alone. -/
@[simp] theorem Operand.read_reg_write_xmm {σ : Type} [PhysicalMemory σ] {m : Nat}
    (s : X86.State σ) (r : BitVec 5) (x : BitVec 5) (v : BitVec 128) :
    (Operand.reg r : Operand m).read ((Operand.xmm x : Operand 128).write s v) =
      (Operand.reg r : Operand m).read s := rfl

/-- `writeFlagsOutputs` changes neither registers nor memory, so operand reads are as before. -/
@[simp] theorem Operand.read_writeFlagsOutputs {σ : Type} [PhysicalMemory σ] {n : Nat} (s : X86.State σ)
    (f : StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) (op : Operand n) :
    op.read (writeFlagsOutputs s f oracleUsed nextIP) = op.read s := by
  have hd : dfBit (writeFlagsOutputs s f oracleUsed nextIP).RFLAGS = dfBit s.RFLAGS :=
    dfBit_store f s.RFLAGS
  exact Operand.read_of_eq (s := writeFlagsOutputs s f oracleUsed nextIP) (t := s)
    rfl rfl rfl rfl hd rfl rfl rfl rfl rfl op

/-- MXCSR as a 32-bit operand is the register. -/
@[simp] theorem Operand.read_mxcsr {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (Operand.mxcsr : Operand 32).read s = s.MXCSR := by
  simp [Operand.read]

/-- A 32-bit MXCSR write replaces the register. -/
@[simp] theorem Operand.write_mxcsr {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (v : BitVec 32) : (Operand.mxcsr : Operand 32).write s v = { s with MXCSR := v } := by
  simp [Operand.write]

/-- An MXCSR write leaves the general-purpose registers, XMM registers and memory alone. -/
theorem Operand.read_write_mxcsr_of_ne {σ : Type} [PhysicalMemory σ] {m n : Nat}
    (s : X86.State σ) (op : Operand m) (hop : op ≠ .mxcsr) (v : BitVec n) :
    op.read ((Operand.mxcsr : Operand n).write s v) = op.read s := by
  cases op <;> first | exact absurd rfl hop | rfl

/-- DF as a 1-bit operand is RFLAGS bit 10. -/
@[simp] theorem Operand.read_df {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (Operand.df : Operand 1).read s = dfBit s.RFLAGS := by
  simp [Operand.read]

/-- A 1-bit DF write sets RFLAGS bit 10, as lean-x86's `RFLAGS.setDF` does. -/
@[simp] theorem Operand.write_df {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (v : BitVec 1) :
    (Operand.df : Operand 1).write s v =
      { s with RFLAGS := X86.Runtime.setSlice s.RFLAGS 10 1 v } := by
  simp [Operand.write]

/-- A DF write leaves the general-purpose registers, XMM registers, MXCSR and memory alone. -/
theorem Operand.read_write_df_of_ne {σ : Type} [PhysicalMemory σ] {m n : Nat}
    (s : X86.State σ) (op : Operand m) (hop : op ≠ .df) (v : BitVec n) :
    op.read ((Operand.df : Operand n).write s v) = op.read s := by
  cases op <;> first | exact absurd rfl hop | rfl

/-- MMX register `r` as a 64-bit operand: the low 64 bits of physical register R`r`. -/
@[simp] theorem Operand.read_mmx {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3) :
    (Operand.mmx r : Operand 64).read s = s.FP87[fprIndex r].setWidth 64 := rfl

/-- A 64-bit MMX write sets physical register R`r` to `0xFFFF ++ v`. -/
@[simp] theorem Operand.write_mmx {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3)
    (v : BitVec 64) :
    (Operand.mmx r : Operand 64).write s v =
      { s with FP87 := Vector.set s.FP87 (fprIndex r) (mmxFpr v) } := by
  simp [Operand.write]

/-- Physical x87 register R`r` as an 80-bit operand. -/
@[simp] theorem Operand.read_fpr {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3) :
    (Operand.fpr r : Operand 80).read s = s.FP87[fprIndex r] := by
  simp [Operand.read]

/-- An 80-bit write of physical x87 register R`r`. -/
@[simp] theorem Operand.write_fpr {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 3)
    (v : BitVec 80) :
    (Operand.fpr r : Operand 80).write s v =
      { s with FP87 := Vector.set s.FP87 (fprIndex r) v } := by
  simp [Operand.write]

/-- The status word as a 16-bit operand: the word without its condition codes. -/
@[simp] theorem Operand.read_fsw {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (Operand.fsw : Operand 16).read s = fswRest s.FP87_Status := by
  simp [Operand.read]

/-- A status-word write sets the bits outside the condition codes. -/
@[simp] theorem Operand.write_fsw {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (v : BitVec 16) :
    (Operand.fsw : Operand 16).write s v =
      { s with FP87_Status := fswMerge v s.FP87_Status } := by
  simp [Operand.write]

/-- The condition codes selected by `m` as a 4-bit operand. -/
@[simp] theorem Operand.read_fcc {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (m : BitVec 4) :
    (Operand.fcc m : Operand 4).read s = fswCC s.FP87_Status &&& m := by
  simp [Operand.read]

/-- A write of the condition codes selected by `m`. -/
@[simp] theorem Operand.write_fcc {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (m v : BitVec 4) :
    (Operand.fcc m : Operand 4).write s v =
      { s with FP87_Status := fswSetCC s.FP87_Status m v } := by
  simp [Operand.write]

/-- The tag word as a 16-bit operand. -/
@[simp] theorem Operand.read_ftw {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (Operand.ftw : Operand 16).read s = s.FP87_Tag_Word := by
  simp [Operand.read]

@[simp] theorem Operand.write_ftw {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (v : BitVec 16) :
    (Operand.ftw : Operand 16).write s v = { s with FP87_Tag_Word := v } := by
  simp [Operand.write]

/-- The control word as a 16-bit operand. -/
@[simp] theorem Operand.read_fcw {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (Operand.fcw : Operand 16).read s = s.FP87_Control := by
  simp [Operand.read]

@[simp] theorem Operand.write_fcw {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (v : BitVec 16) :
    (Operand.fcw : Operand 16).write s v = { s with FP87_Control := v } := by
  simp [Operand.write]

/-- The last-instruction pointers as a 171-bit operand. -/
@[simp] theorem Operand.read_fpuPtr {σ : Type} [PhysicalMemory σ] (s : X86.State σ) :
    (Operand.fpuPtr : Operand 171).read s = fpuPtrOf s := by
  simp [Operand.read]

@[simp] theorem Operand.write_fpuPtr {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (v : BitVec 171) : (Operand.fpuPtr : Operand 171).write s v = setFpuPtr s v := by
  simp [Operand.write, setFpuPtr]

/-- An operand outside the x87 state: a general-purpose register, memory, an XMM register, MXCSR
or DF. -/
def Operand.NotX87 {n : Nat} : Operand n → Prop
  | .fpr _ | .mmx _ | .fsw | .ftw | .fcw | .fpuPtr | .fcc _ => False
  | _ => True

/-- An operand an effect may read: anything but the x87 condition codes (`Operand.fcc`), which
the composition of effects does not track (they are often undefined). -/
@[simp] def Operand.Visible {n : Nat} : Operand n → Prop
  | .reg _ | .mem _ | .xmm _ | .regHigh _ | .mxcsr | .df | .fpr _ | .mmx _ | .fsw | .ftw | .fcw
  | .fpuPtr => True
  | .fcc _ => False

/-- Every byte register is an operand an effect may read. -/
@[simp] theorem Operand.visible_gpr8 (r : BitVec 5) (rex : Bool) :
    (Operand.gpr8 r rex).Visible := by
  unfold Operand.gpr8
  split <;> trivial

@[simp] theorem Operand.visible_byteReg (r : BitVec 3) : (Operand.byteReg r).Visible :=
  Operand.visible_gpr8 _ _

/-- A write of the x87 state leaves every operand outside it alone. -/
theorem Operand.read_write_x87 {σ : Type} [PhysicalMemory σ] {m n : Nat} (s : X86.State σ)
    (op : Operand m) (hop : op.NotX87) (dst : Operand n) (hdst : ¬ dst.NotX87) (v : BitVec n) :
    op.read (dst.write s v) = op.read s := by
  cases dst <;> (try exact absurd trivial hdst) <;> cases op <;> (try exact hop.elim) <;> rfl

/-- A write outside the x87 state leaves the x87 operands alone. -/
theorem Operand.read_x87_write {σ : Type} [PhysicalMemory σ] {m n : Nat} (s : X86.State σ)
    (op : Operand m) (hop : ¬ op.NotX87) (dst : Operand n) (hdst : dst.NotX87) (v : BitVec n) :
    op.read (dst.write s v) = op.read s := by
  cases op <;> (try exact absurd trivial hop) <;> cases dst <;> (try exact hdst.elim) <;>
    first | rfl | simp [Operand.read, Operand.write, dfBit]

end X86Proofs
