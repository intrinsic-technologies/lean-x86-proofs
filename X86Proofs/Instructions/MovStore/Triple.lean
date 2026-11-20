import X86Proofs.Instructions.MovStore.Step
import X86Proofs.Instructions.MovStore.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

/-!
# Store triples

A memory operand given by an `AddrMode` `am`; an instruction of `len` bytes at `p` writes the
operand at `am.addr s (p + len)` in the start state `s` (for a RIP-relative operand, relative to
the instruction's end `p + len`). All are derived from the step theorems by `Triple.of_store`
(`Program/ReadWrite/Store.lean`), with effect `storeEffect`:

| Instruction | Bytes | `len` | Triple (any bytes / convenience) | Effect |
|---|---|---|---|---|
| `mov [am], r64` | `REX.W 89 /r` | `3 + tail` | `mov_m64_r64_triple_of_bytes` / `mov_m64_r64_triple` | `movM64R64Effect` |
| `mov [am], r32` | `REX 89 /r`, W = 0 | `3 + tail` | `mov_m32_r32_triple_of_bytes` | `movM32R32Effect` |
| `mov qword [am], imm32` | `REX.W C7 /0 id` | `7 + tail` | `mov_m64_imm32_triple_of_bytes` / `mov_m64_imm32_triple` | `movM64Imm32Effect` |
| `mov word [am], imm16` | `66 C7 /0 iw` | `5 + tail` | `mov_m16_imm16_triple` | `movM16Imm16Effect` |
| `mov byte [am], imm8` | `C6 /0 ib` | `3 + tail` | `mov_m8_imm8_triple` | `movM8Imm8Effect` |
| `mov byte [am], imm8`, REX | `REX C6 /0 ib` | `4 + tail` | `mov_m8_imm8_rex_triple_of_bytes` | `movM8Imm8RexEffect` |
| `mov qword fs:[am], imm32` | `64`/`65`, `REX.W C7 /0 id` | `8 + tail` | `mov_m64_imm32_seg_triple_of_bytes` / `mov_m64_imm32_seg_triple` | `movM64Imm32SegEffect` |
| `mov word fs:[am], imm16` | `64`/`65`, `66 C7 /0 iw` | `6 + tail` | `mov_m16_imm16_seg_triple` | `movM16Imm16SegEffect` |
| `mov byte fs:[am], imm8` | `64`/`65`, `C6 /0 ib` | `4 + tail` | `mov_m8_imm8_seg_triple` | `movM8Imm8SegEffect` |
| `mov qword [am], imm32`, address size 32 | `67 REX.W C7 /0 id` | `8 + tail` | `mov_m64_imm32_a32_triple_of_bytes` / `mov_m64_imm32_a32_triple` | `movM64Imm32A32Effect` |
| `mov word [am], imm16`, address size 32 | `67 66 C7 /0 iw` | `6 + tail` | `mov_m16_imm16_a32_triple` | `movM16Imm16A32Effect` |
| `mov byte [am], imm8`, address size 32 | `67 C6 /0 ib` | `4 + tail` | `mov_m8_imm8_a32_triple` | `movM8Imm8A32Effect` |

Precondition: `StorePre p len (fun s => am.addr s (p + len)) (n / 8)`: RIP = `p`, the bytes written
are below 4 GiB (they may cross a page), present in RAM and none of the page-table entries
(`PageTableEntriesApart`), and miss the instruction's own bytes. The effect writes only those
bytes (and RIP): registers and flags are unchanged. Behind an FS/GS prefix (`r : SegReg`,
`r.prefixByte`) the precondition is
`SegStorePre p len r base (fun s => am.addr s (p + len)) (n / 8)` (the segment ready with base
`base`, `StorePre` at `base` plus the offset) and the effect writes there. Behind `67` (address
size 32) the operand is at `am.addr32 s (p + len)` instead.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The address a store of `len` bytes' instruction at `p` with addressing `am` writes in state
`s`. -/
abbrev storeAddrAt (p : BitVec 64) (am : AddrMode) (len : Nat) (s : RamState) : BitVec 64 :=
  am.addr s (p + BitVec.ofNat 64 len)

/-- The effect of `mov qword [am], src` at `p`: the 8 bytes at the operand's address set to the
64-bit register `src`. -/
def movM64R64Effect (p : BitVec 64) (src : BitVec 5) (am : AddrMode) : RamState → Effect :=
  storeEffect p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length))
    fun s => (Operand.reg src : Operand 64).read s

/-- The effect of `mov dword [am], src32` at `p`: the 4 bytes at the operand's address set to the
low 32 bits of register `src`. -/
def movM32R32Effect (p : BitVec 64) (src : BitVec 5) (am : AddrMode) : RamState → Effect :=
  storeEffect p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length))
    fun s => (Operand.reg src : Operand 32).read s

/-- The effect of `mov qword [am], imm32` at `p`: the 8 bytes at the operand's address set to the
immediate sign-extended to 64 bits. -/
def movM64Imm32Effect (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) : RamState → Effect :=
  storeEffect p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length))
    fun _ => imm.signExtend 64

/-- The effect of `mov word [am], imm16` at `p`: the 2 bytes at the operand's address set to the
immediate. -/
def movM16Imm16Effect (p : BitVec 64) (am : AddrMode) (imm : BitVec 16) : RamState → Effect :=
  storeEffect p (5 + am.tail.length) (storeAddrAt p am (5 + am.tail.length)) fun _ => imm

/-- The effect of `mov byte [am], imm8` at `p`: the byte at the operand's address set to the
immediate. -/
def movM8Imm8Effect (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) : RamState → Effect :=
  storeEffect p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) fun _ => imm

/-- The effect of `mov byte [am], imm8` with a REX prefix (for a shape that needs REX.X or REX.B)
at `p`: the byte at the operand's address set to the immediate. -/
def movM8Imm8RexEffect (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) : RamState → Effect :=
  storeEffect p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)) fun _ => imm

@[simp] theorem movM64R64Effect_components (p : BitVec 64) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : (movM64R64Effect p src am s).components =
      [.mem (storeAddrAt p am (3 + am.tail.length) s) 8, .rip] := by
  simp [movM64R64Effect]

@[simp] theorem movM32R32Effect_components (p : BitVec 64) (src : BitVec 5) (am : AddrMode)
    (s : RamState) : (movM32R32Effect p src am s).components =
      [.mem (storeAddrAt p am (3 + am.tail.length) s) 4, .rip] := by
  simp [movM32R32Effect]

@[simp] theorem movM64Imm32Effect_components (p : BitVec 64) (am : AddrMode) (imm : BitVec 32)
    (s : RamState) : (movM64Imm32Effect p am imm s).components =
      [.mem (storeAddrAt p am (7 + am.tail.length) s) 8, .rip] := by
  simp [movM64Imm32Effect]

@[simp] theorem movM16Imm16Effect_components (p : BitVec 64) (am : AddrMode) (imm : BitVec 16)
    (s : RamState) : (movM16Imm16Effect p am imm s).components =
      [.mem (storeAddrAt p am (5 + am.tail.length) s) 2, .rip] := by
  simp [movM16Imm16Effect]

@[simp] theorem movM8Imm8Effect_components (p : BitVec 64) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : (movM8Imm8Effect p am imm s).components =
      [.mem (storeAddrAt p am (3 + am.tail.length) s) 1, .rip] := by
  simp [movM8Imm8Effect]

@[simp] theorem movM8Imm8RexEffect_components (p : BitVec 64) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : (movM8Imm8RexEffect p am imm s).components =
      [.mem (storeAddrAt p am (4 + am.tail.length) s) 1, .rip] := by
  simp [movM8Imm8RexEffect]

/-- The code bound a step theorem takes, from the code being in memory. -/
theorem CodeIn.low_len {p : BitVec 64} {bytes : List UInt8} {s : RamState}
    (h : CodeIn (codeRange p bytes) s) {len : Nat} (hlen : bytes.length = len) (hpos : 0 < len)
    (h15 : len ≤ 15) : p.toNat + len ≤ 2^32 := by
  have := h.low (by omega) (by omega)
  omega

/-! ### `89 /r` -/

/-- The step behind `mov_m64_r64_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `movM64R64Effect`. -/
theorem mov_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  StepEffect.of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

/-- The triple for `mov qword [am], r64` (`REX.W 89 /r`, `mod ≠ 3`) at `p`, for any addressing
shape `am` and `reg` field: the effect `movM64R64Effect` on the `reg` register extended by
REX.R. -/
theorem mov_m64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m64_r64_effect_step p rex hrex reg am hv hx hb)

/-- The step behind `mov_m32_r32_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `movM32R32Effect`. -/
theorem mov_m32_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

/-- The triple for `mov dword [am], r32` (`REX 89 /r` with W = 0, `mod ≠ 3`) at `p`: the effect
`movM32R32Effect` on the `reg` register extended by REX.R. -/
theorem mov_m32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_r32_effect_step p rex hrex reg am hv hx hb)

/-! ### `C7 /0`, `C6 /0` -/

/-- The step behind `mov_m64_imm32_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movM64Imm32Effect`.
-/
theorem mov_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32Effect p am imm) :=
  StepEffect.of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_imm32_step s h rex hrex am hv hx hb imm hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

/-- The triple for `mov qword [am], imm32` (`REX.W C7 /0 id`, `mod ≠ 3`) at `p`: the effect
`movM64Imm32Effect`. -/
theorem mov_m64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM64Imm32Effect p am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m64_imm32_effect_step p rex hrex am hv hx hb imm)

/-- The step behind `mov_m16_imm16_triple`: from a ready state with the instruction in memory and
the precondition, one `step` reaches a ready state with the effect `movM16Imm16Effect`. -/
theorem mov_m16_imm16_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (StorePre p (5 + am.tail.length) (storeAddrAt p am (5 + am.tail.length)) 2)
      (codeRange p (0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
      (movM16Imm16Effect p am imm) := by
  have hse : imm.signExtend 16 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have := mov_m16_imm16_step s h am hv hx hb imm hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hw
  rwa [movSpec, hse] at this

/-- The triple for `mov word [am], imm16` (`66 C7 /0 iw`, `mod ≠ 3`) at `p`, for a shape that
needs neither REX.X nor REX.B: the effect `movM16Imm16Effect`. -/
theorem mov_m16_imm16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (StorePre p (5 + am.tail.length) (storeAddrAt p am (5 + am.tail.length)) 2)
      (codeRange p (0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (movM16Imm16Effect p am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m16_imm16_effect_step p am hv hx hb imm)

/-- The step behind `mov_m8_imm8_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `movM8Imm8Effect`. -/
theorem mov_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8Effect p am imm) := by
  have hse : imm.signExtend 8 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have := mov_m8_imm8_step s h am hv hx hb imm hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hw
  rwa [movSpec, hse] at this

/-- The triple for `mov byte [am], imm8` (`C6 /0 ib`, `mod ≠ 3`, no prefix) at `p`, for a shape
that needs neither REX.X nor REX.B: the effect `movM8Imm8Effect`. -/
theorem mov_m8_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (movM8Imm8Effect p am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_imm8_effect_step p am hv hx hb imm)

/-- The step behind `mov_m8_imm8_rex_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect
`movM8Imm8RexEffect`. -/
theorem mov_m8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (StorePre p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)) 1)
      (codeRange p (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8RexEffect p am imm) := by
  have hse : imm.signExtend 8 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  have hstep := mov_m8_imm8_prefix_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  simp only [scanContext_rex _ _ hr] at hstep
  rwa [movSpec, hse] at hstep

/-- The triple for `mov byte [am], imm8` with a REX prefix (`REX C6 /0 ib`, `mod ≠ 3`) at `p`, for
any shape (REX.X and REX.B as it needs): the effect `movM8Imm8RexEffect`. -/
theorem mov_m8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (StorePre p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)) 1)
      (codeRange p (rex :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (movM8Imm8RexEffect p am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_imm8_rex_effect_step p rex hr am hv hx hb imm)

/-! ### Registers by number (encoders in `Encode.lean`) -/

/-- The triple for `mov qword [am], src` on the 64-bit register numbered `src` at `p`, in the
encoding `encodeMovM64R64`: the effect `movM64R64Effect` on that register. -/
theorem mov_m64_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (encodeMovM64R64 src am)) (Effect.post (movM64R64Effect p (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := mov_m64_r64_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

/-- The triple for `mov qword [am], imm32` at `p`, in the encoding `encodeMovM64Imm32`. -/
theorem mov_m64_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (encodeMovM64Imm32 am imm)) (Effect.post (movM64Imm32Effect p am imm)) := by
  obtain ⟨hrex, _, hx, hb⟩ := am.rexByte_true_spec 0
  exact mov_m64_imm32_triple_of_bytes p _ hrex am hv hx hb imm

/-! ### Immediate stores through FS or GS

The instructions above behind a segment-override prefix `r.prefixByte` (`64` for FS, `65` for
GS; `r : SegReg`): the store is at the operand's offset plus the segment's base `base`, under
`SegStorePre` (the segment ready with base `base`, `StorePre` at the linear address). The step
theorems are `mov_m_imm32_prefix_step`, `mov_m16_imm16_prefix_step` and
`mov_m8_imm8_prefix_step`. -/

/-- The effect of `mov qword fs:[am], imm32` (or `gs:`) at `p`: the 8 bytes at `base` plus the
operand's offset set to the immediate sign-extended to 64 bits. -/
def movM64Imm32SegEffect (p base : BitVec 64) (am : AddrMode) (imm : BitVec 32) :
    RamState → Effect :=
  storeEffect p (8 + am.tail.length) (fun s => base + storeAddrAt p am (8 + am.tail.length) s)
    fun _ => imm.signExtend 64

/-- The effect of `mov word fs:[am], imm16` (or `gs:`) at `p`: the 2 bytes at `base` plus the
operand's offset set to the immediate. -/
def movM16Imm16SegEffect (p base : BitVec 64) (am : AddrMode) (imm : BitVec 16) :
    RamState → Effect :=
  storeEffect p (6 + am.tail.length) (fun s => base + storeAddrAt p am (6 + am.tail.length) s)
    fun _ => imm

/-- The effect of `mov byte fs:[am], imm8` (or `gs:`) at `p`: the byte at `base` plus the
operand's offset set to the immediate. -/
def movM8Imm8SegEffect (p base : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    RamState → Effect :=
  storeEffect p (4 + am.tail.length) (fun s => base + storeAddrAt p am (4 + am.tail.length) s)
    fun _ => imm

/-- The step behind `mov_m64_imm32_seg_triple_of_bytes`: `mov_m64_imm32_effect_step` behind an
FS/GS prefix. -/
theorem mov_m64_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (SegStorePre p (8 + am.tail.length) r base (storeAddrAt p am (8 + am.tail.length)) 8)
      (codeRange p (r.prefixByte :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32SegEffect p base am imm) :=
  StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
      subst hp hbase
      have := am.tail_length_le
      have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 :=
        hcode.low_len (by simp; omega) (by omega) (by omega)
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
          withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
        rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil),
          scanContext_rex _ _ hr]
      have hstep := mov_m_imm32_prefix_step s h [r.prefixByte, rex]
        (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
        (by rw [hsc]; exact hrex.operand_size s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
        imm hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      exact hstep

/-- The triple for `mov qword fs:[am], imm32` (or `gs:`; `r.prefixByte`, then `REX.W C7 /0 id`)
at `p`: the effect `movM64Imm32SegEffect`. -/
theorem mov_m64_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 32) :
    Triple (SegStorePre p (8 + am.tail.length) r base (storeAddrAt p am (8 + am.tail.length)) 8)
      (codeRange p (r.prefixByte :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM64Imm32SegEffect p base am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m64_imm32_seg_effect_step p r base rex hrex am hv hx hb imm)

/-- The triple for `mov qword fs:[am], imm32` (or `gs:`) at `p`, in the encoding
`encodeMovM64Imm32` behind the prefix. -/
theorem mov_m64_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) :
    Triple (SegStorePre p (8 + am.tail.length) r base (storeAddrAt p am (8 + am.tail.length)) 8)
      (codeRange p (r.prefixByte :: encodeMovM64Imm32 am imm))
      (Effect.post (movM64Imm32SegEffect p base am imm)) := by
  obtain ⟨hrex, _, hx, hb⟩ := am.rexByte_true_spec 0
  exact mov_m64_imm32_seg_triple_of_bytes p r base _ hrex am hv hx hb imm

/-- The step behind `mov_m16_imm16_seg_triple`: `mov_m16_imm16_effect_step` behind an FS/GS
prefix (`r.prefixByte`, then `66 C7 /0 iw`). -/
theorem mov_m16_imm16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (SegStorePre p (6 + am.tail.length) r base (storeAddrAt p am (6 + am.tail.length)) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
      (movM16Imm16SegEffect p base am imm) := by
  have hse : imm.signExtend 16 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => ?_
  obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
  subst hp hbase
  have := am.tail_length_le
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (oszContext s.DS) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil),
      scanContext_66]
  have hstep := mov_m16_imm16_prefix_step s h [r.prefixByte, 0x66]
    (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  rwa [movSpec, hse] at hstep

/-- The triple for `mov word fs:[am], imm16` (or `gs:`; `r.prefixByte`, then `66 C7 /0 iw`) at
`p`, for a shape that needs neither REX.X nor REX.B: the effect `movM16Imm16SegEffect`. -/
theorem mov_m16_imm16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (SegStorePre p (6 + am.tail.length) r base (storeAddrAt p am (6 + am.tail.length)) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (movM16Imm16SegEffect p base am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m16_imm16_seg_effect_step p r base am hv hx hb imm)

/-- The step behind `mov_m8_imm8_seg_triple`: `mov_m8_imm8_effect_step` behind an FS/GS prefix
(`r.prefixByte`, then `C6 /0 ib`). -/
theorem mov_m8_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegStorePre p (4 + am.tail.length) r base (storeAddrAt p am (4 + am.tail.length)) 1)
      (codeRange p (r.prefixByte :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8SegEffect p base am imm) := by
  have hse : imm.signExtend 8 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => ?_
  obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
  subst hp hbase
  have := am.tail_length_le
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (legacyContext s.DS) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil, scanContext_nil]
  have hstep := mov_m8_imm8_prefix_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  rwa [movSpec, hse] at hstep

/-- The triple for `mov byte fs:[am], imm8` (or `gs:`; `r.prefixByte`, then `C6 /0 ib`) at `p`,
for a shape that needs neither REX.X nor REX.B: the effect `movM8Imm8SegEffect`. -/
theorem mov_m8_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegStorePre p (4 + am.tail.length) r base (storeAddrAt p am (4 + am.tail.length)) 1)
      (codeRange p (r.prefixByte :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (movM8Imm8SegEffect p base am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m8_imm8_seg_effect_step p r base am hv hx hb imm)

/-! ### Immediate stores at address size 32

The immediate stores behind an address-size prefix `67` (first): the store is at
`am.addr32 s (p + len)` (`AddrMode.addr32`, the low 32 bits of the address, zero-extended), under
`StorePre` there. The effects take the length as a parameter. The step theorems are
`mov_m_imm32_prefix_a32_step`, `mov_m16_imm16_prefix_a32_step` and `mov_m8_imm8_prefix_a32_step`. -/

/-- The effect of `mov qword [am], imm32` behind `67` (an instruction of `len` bytes at `p`): the 8
bytes at the operand's 32-bit address set to the immediate sign-extended to 64 bits. -/
def movM64Imm32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun _ => imm.signExtend 64

/-- The effect of `mov word [am], imm16` behind `67`: the 2 bytes at the operand's 32-bit address
set to the immediate. -/
def movM16Imm16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 16) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun _ => imm

/-- The effect of `mov byte [am], imm8` behind `67`: the byte at the operand's 32-bit address set
to the immediate. -/
def movM8Imm8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun _ => imm

/-- The step behind `mov_m64_imm32_a32_triple_of_bytes`. -/
theorem mov_m64_imm32_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (StorePre p (8 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32A32Effect p (8 + am.tail.length) am imm) :=
  StepEffect.of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 :=
        hcode.low_len (by simp; omega) (by omega) (by omega)
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
          withAsz (rexContext s.DS rex.toBitVec) := by
        rw [scanContext_asz_cons, scanContext_rex _ _ hr]
      have hstep := mov_m_imm32_prefix_a32_step s h [0x67, rex]
        (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
        (by rw [hsc]; exact hrex.operand_size s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
        imm hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      exact hstep

/-- The triple for `mov qword [am], imm32` behind `67` (`67 REX.W C7 /0 id`) at `p`: the effect
`movM64Imm32A32Effect`. -/
theorem mov_m64_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (StorePre p (8 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM64Imm32A32Effect p (8 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m64_imm32_a32_effect_step p rex hrex am hv hx hb imm)

/-- The triple for `mov qword [am], imm32` behind `67` at `p`, in the encoding
`encodeMovM64Imm32`. -/
theorem mov_m64_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (StorePre p (8 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 8)
      (codeRange p (0x67 :: encodeMovM64Imm32 am imm))
      (Effect.post (movM64Imm32A32Effect p (8 + am.tail.length) am imm)) := by
  obtain ⟨hrex, _, hx, hb⟩ := am.rexByte_true_spec 0
  exact mov_m64_imm32_a32_triple_of_bytes p _ hrex am hv hx hb imm

/-- The step behind `mov_m16_imm16_a32_triple` (`67 66 C7 /0 iw`). -/
theorem mov_m16_imm16_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    StepEffect (StorePre p (6 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
      (movM16Imm16A32Effect p (6 + am.tail.length) am imm) := by
  have hse : imm.signExtend 16 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] = withAsz (oszContext s.DS) := by
    rw [scanContext_asz_cons, scanContext_66]
  have hstep := mov_m16_imm16_prefix_a32_step s h [0x67, 0x66]
    (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm hcode.bytesAt hlow
    (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  rwa [movSpec, hse] at hstep

/-- The triple for `mov word [am], imm16` behind `67` (`67 66 C7 /0 iw`) at `p`, for a shape that
needs neither REX.X nor REX.B: the effect `movM16Imm16A32Effect`. -/
theorem mov_m16_imm16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16) :
    Triple (StorePre p (6 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
      (Effect.post (movM16Imm16A32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m16_imm16_a32_effect_step p am hv hx hb imm)

/-- The step behind `mov_m8_imm8_a32_triple` (`67 C6 /0 ib`). -/
theorem mov_m8_imm8_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8A32Effect p (4 + am.tail.length) am imm) := by
  have hse : imm.signExtend 8 = imm := BitVec.signExtend_eq imm
  refine StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 :=
    hcode.low_len (by simp; omega) (by omega) (by omega)
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] = withAsz (legacyContext s.DS) := by
    rw [scanContext_asz_cons, scanContext_nil]
  have hstep := mov_m8_imm8_prefix_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp) (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm hcode.bytesAt hlow
    (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  rwa [movSpec, hse] at hstep

/-- The triple for `mov byte [am], imm8` behind `67` (`67 C6 /0 ib`) at `p`, for a shape that
needs neither REX.X nor REX.B: the effect `movM8Imm8A32Effect`. -/
theorem mov_m8_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (movM8Imm8A32Effect p (4 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_imm8_a32_effect_step p am hv hx hb imm)

/-! ### Examples: encodings of stores -/

/-- `mov [rsp - 0x38], rcx` (`48 89 4C 24 C8`). -/
example : encodeMovM64R64 1 (.sib 4 none 0 (.d8 0xC8)) = [0x48, 0x89, 0x4C, 0x24, 0xC8] := by
  decide
/-- `mov [rsp], rdi` (`48 89 3C 24`). -/
example : encodeMovM64R64 7 (.sib 4 none 0 .none) = [0x48, 0x89, 0x3C, 0x24] := by decide
/-- `mov [rcx + 0x90], r15` (`4C 89 B9 90 00 00 00`). -/
example : encodeMovM64R64 15 (.base 1 (.d32 0x90)) = [0x4C, 0x89, 0xB9, 0x90, 0x00, 0x00, 0x00] := by
  decide
/-- `mov [rcx + 0x30], r12` (`4C 89 61 30`). -/
example : encodeMovM64R64 12 (.base 1 (.d8 0x30)) = [0x4C, 0x89, 0x61, 0x30] := by decide
/-- `mov [rsp + 0xD8], r14` (`4C 89 B4 24 D8 00 00 00`). -/
example : encodeMovM64R64 14 (.sib 4 none 0 (.d32 0xD8)) =
    [0x4C, 0x89, 0xB4, 0x24, 0xD8, 0x00, 0x00, 0x00] := by decide
/-- `movq $0x88, 0xE0(%rsp)` (`48 C7 84 24 E0 00 00 00 88 00 00 00`). -/
example : encodeMovM64Imm32 (.sib 4 none 0 (.d32 0xE0)) 0x88 =
    [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x88, 0x00, 0x00, 0x00] := by decide
/-- `movw $0x1, 0xE8(%rsp)` (`66 C7 84 24 E8 00 00 00 01 00`). -/
example : (0x66 : UInt8) :: 0xC7 :: (AddrMode.sib 4 none 0 (.d32 0xE8)).modrm 0 ::
    ((AddrMode.sib 4 none 0 (.d32 0xE8)).tail ++ immBytes 16 1) =
    [0x66, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x01, 0x00] := by decide
/-- `movb $0x1, 0x1D1(%rsp)` (`C6 84 24 D1 01 00 00 01`). -/
example : (0xC6 : UInt8) :: (AddrMode.sib 4 none 0 (.d32 0x1D1)).modrm 0 ::
    ((AddrMode.sib 4 none 0 (.d32 0x1D1)).tail ++ immBytes 8 1) =
    [0xC6, 0x84, 0x24, 0xD1, 0x01, 0x00, 0x00, 0x01] := by decide
/-- `movb $0x80, 0x8(%rsp,%r15,1)` (`42 C6 44 3C 08 80`): REX.X for the index R15. -/
example : (0x42 : UInt8) :: 0xC6 :: (AddrMode.sib 4 (some 15) 0 (.d8 0x08)).modrm 0 ::
    ((AddrMode.sib 4 (some 15) 0 (.d8 0x08)).tail ++ immBytes 8 0x80) =
    [0x42, 0xC6, 0x44, 0x3C, 0x08, 0x80] := by decide

/-- `movw $0x1, 0xE8(%rsp)` at `p`, as a triple on its literal bytes. -/
example [Bindings] (p : BitVec 64) :
    Triple (StorePre p 10 (storeAddrAt p (.sib 4 none 0 (.d32 0xE8)) 10) 2)
      (codeRange p [0x66, 0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x01, 0x00])
      (Effect.post (movM16Imm16Effect p (.sib 4 none 0 (.d32 0xE8)) 1)) :=
  mov_m16_imm16_triple p (.sib 4 none 0 (.d32 0xE8)) ⟨by decide, by decide⟩ (by decide) (by decide) 1

attribute [x86_compose] movM64R64Effect movM32R32Effect movM64Imm32Effect movM16Imm16Effect
  movM8Imm8Effect movM8Imm8RexEffect storeAddrAt movM64Imm32SegEffect movM16Imm16SegEffect
  movM8Imm8SegEffect movM64Imm32A32Effect movM16Imm16A32Effect movM8Imm8A32Effect

@[x86_local] theorem movM64R64Effect_local {p : BitVec 64} {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM64R64Effect p src am) := by
  effect_local [movM64R64Effect, storeEffect]

@[x86_local] theorem movM32R32Effect_local {p : BitVec 64} {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM32R32Effect p src am) := by
  effect_local [movM32R32Effect, storeEffect]

@[x86_local] theorem movM64Imm32Effect_local {p : BitVec 64} {am : AddrMode} {imm32 : BitVec 32} :
    Effect.Local (movM64Imm32Effect p am imm32) := by
  effect_local [movM64Imm32Effect, storeEffect]

@[x86_local] theorem movM16Imm16Effect_local {p : BitVec 64} {am : AddrMode} {imm16 : BitVec 16} :
    Effect.Local (movM16Imm16Effect p am imm16) := by
  effect_local [movM16Imm16Effect, storeEffect]

@[x86_local] theorem movM8Imm8Effect_local {p : BitVec 64} {am : AddrMode} {imm8 : BitVec 8} :
    Effect.Local (movM8Imm8Effect p am imm8) := by
  effect_local [movM8Imm8Effect, storeEffect]

@[x86_local] theorem movM8Imm8RexEffect_local {p : BitVec 64} {am : AddrMode} {imm8 : BitVec 8} :
    Effect.Local (movM8Imm8RexEffect p am imm8) := by
  effect_local [movM8Imm8RexEffect, storeEffect]

@[x86_local] theorem movM64Imm32SegEffect_local {p base : BitVec 64} {am : AddrMode}
    {imm32 : BitVec 32} : Effect.Local (movM64Imm32SegEffect p base am imm32) := by
  effect_local [movM64Imm32SegEffect, storeEffect]

@[x86_local] theorem movM16Imm16SegEffect_local {p base : BitVec 64} {am : AddrMode}
    {imm16 : BitVec 16} : Effect.Local (movM16Imm16SegEffect p base am imm16) := by
  effect_local [movM16Imm16SegEffect, storeEffect]

@[x86_local] theorem movM8Imm8SegEffect_local {p base : BitVec 64} {am : AddrMode}
    {imm8 : BitVec 8} : Effect.Local (movM8Imm8SegEffect p base am imm8) := by
  effect_local [movM8Imm8SegEffect, storeEffect]

@[x86_local] theorem movM64Imm32A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm32 : BitVec 32} : Effect.Local (movM64Imm32A32Effect p len am imm32) := by
  effect_local [movM64Imm32A32Effect, storeEffect]

@[x86_local] theorem movM16Imm16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm16 : BitVec 16} : Effect.Local (movM16Imm16A32Effect p len am imm16) := by
  effect_local [movM16Imm16A32Effect, storeEffect]

@[x86_local] theorem movM8Imm8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm8 : BitVec 8} : Effect.Local (movM8Imm8A32Effect p len am imm8) := by
  effect_local [movM8Imm8A32Effect, storeEffect]

attribute [x86_addr] storeAddrAt

end X86Proofs
