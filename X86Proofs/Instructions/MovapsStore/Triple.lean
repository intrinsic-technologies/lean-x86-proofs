import X86Proofs.Instructions.MovapsStore.Step
import X86Proofs.Instructions.MovapsStore.Encode
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.Compose

/-!
# MOVAPS store triples

`movaps m128, xmm` (`0F 29 /r`, `mod ≠ 3`): the 16 bytes at the destination (an `AddrMode` `am`;
for an instruction of `len` bytes at `p`, the address `am.addr s (p + len)` in the start state `s`)
become the source XMM register's 128 bits. Registers, flags and the rest of memory are unchanged.
The precondition is `SseAlignedStorePre p len (storeAddrAt p am len)`: `StorePre` for 16 bytes
(RIP = `p`, the bytes below 4 GiB, present in RAM, outside the page tables and apart from the
instruction), SSE enabled, and the address a multiple of 16 (else MOVAPS raises #GP). Derived from
the step theorems by `Triple.of_store_pre`, with effect `movapsM128XmmEffect` (a `storeEffect`).

| Bytes | `len` | Triple |
|---|---|---|
| `0F 29 /r` (registers 0–7, no REX.X/REX.B) | `3 + tail` | `movaps_m128_xmm_triple_of_bytes` |
| `rex 0F 29 /r` | `4 + tail` | `movaps_m128_xmm_rex_triple_of_bytes` |
| `encodeMovapsM128Xmm src am` (register number 0–15, shortest) | its length | `movaps_m128_xmm_triple` |
| `64`/`65 0F 29 /r` | `4 + tail` | `movaps_m128_xmm_seg_triple_of_bytes` |
| `64`/`65 rex 0F 29 /r` | `5 + tail` | `movaps_m128_xmm_rex_seg_triple_of_bytes` |
| `r.prefixByte :: encodeMovapsM128Xmm src am` | its length | `movaps_m128_xmm_seg_triple` |

The `_seg` triples (an FS/GS override `r : SegReg`, first) have the effect `movapsM128XmmSegEffect`
(the store at `base + am.addr s (p + len)`) and the precondition `SseAlignedStorePre` at that
address plus `r.Ready base` (the segment ready, with base `base`).

Examples at the end: `0F 29` without a prefix, storing XMM0 or XMM1 to `[rsp + disp8]`,
`[rsp + disp32]` or `[rsp + rcx + disp8]`, and one REX encoding.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of `movaps [am], src` at `p` for an encoding of `len` bytes: the 16 bytes at the
operand's address set to the XMM register `src`. -/
def movapsM128XmmEffect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (storeAddrAt p am len) fun s => (Operand.xmm src : Operand 128).read s

@[simp] theorem movapsM128XmmEffect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movapsM128XmmEffect p len src am s).components =
      [.mem (storeAddrAt p am len s) 16, .rip] := by
  simp [movapsM128XmmEffect]

/-- The step behind `movaps_m128_xmm_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movapsM128XmmEffect`.
-/
theorem movaps_m128_xmm_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SseAlignedStorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)))
      (codeRange p (0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (movapsM128XmmEffect p (3 + am.tail.length) (gprNumber 0 0 reg) am) :=
  StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hsse, halign⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact movaps_m128_xmm_step s h hsse reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) halign hw

/-- The triple for `movaps [am], xmm` (`0F 29 /r`, no prefix, `mod ≠ 3`) at `p`, for any `reg`
field (XMM0–XMM7) and any addressing shape `am` that needs neither REX.X nor REX.B: the effect
`movapsM128XmmEffect` on the `reg` register. -/
theorem movaps_m128_xmm_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SseAlignedStorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)))
      (codeRange p (0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (Effect.post (movapsM128XmmEffect p (3 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movaps_m128_xmm_effect_step p reg am hv hx hb)

/-- The step behind `movaps_m128_xmm_rex_triple_of_bytes`: from a ready state with the instruction
in memory and the precondition, one `step` reaches a ready state with the effect
`movapsM128XmmEffect`. -/
theorem movaps_m128_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SseAlignedStorePre p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)))
      (codeRange p (rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (movapsM128XmmEffect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hsse, halign⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact movaps_m128_xmm_rex_step s h hsse rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) halign hw

/-- The triple for `movaps [am], xmm` after a REX prefix (`rex 0F 29 /r`, `mod ≠ 3`) at `p`, for
any addressing shape `am` (REX.X and REX.B as `am` needs): the effect `movapsM128XmmEffect` on the
`reg` register extended by REX.R. -/
theorem movaps_m128_xmm_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SseAlignedStorePre p (4 + am.tail.length) (storeAddrAt p am (4 + am.tail.length)))
      (codeRange p (rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (Effect.post (movapsM128XmmEffect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movaps_m128_xmm_rex_effect_step p rex hrex reg am hv hx hb)

/-! ### Registers by number (encoder in `Encode.lean`) -/

/--
The triple for `movaps [am], src` on the XMM register numbered `src` (0–15) at `p`, in the
encoding `encodeMovapsM128Xmm src am`, for any valid addressing shape: the effect
`movapsM128XmmEffect` on that register, with the length of that encoding (`3 + tail` without a
prefix, `4 + tail` with one).
-/
theorem movaps_m128_xmm_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (SseAlignedStorePre p (encodeMovapsM128Xmm src am).length
        (storeAddrAt p am (encodeMovapsM128Xmm src am).length))
      (codeRange p (encodeMovapsM128Xmm src am))
      (Effect.post (movapsM128XmmEffect p (encodeMovapsM128Xmm src am).length (src.setWidth 5) am)) := by
  by_cases hlow : am.NoRex src
  · have hbytes : encodeMovapsM128Xmm src am = 0x0F :: 0x29 :: am.modrm (regLow src) :: am.tail :=
      ite_eq_left hlow
    have hlen : (encodeMovapsM128Xmm src am).length = 3 + am.tail.length := by
      rw [hbytes]; simp; omega
    rw [hlen, hbytes, ← gprNumber_reg src, hlow.1]
    exact movaps_m128_xmm_triple_of_bytes p (regLow src) am hv hlow.2.1 hlow.2.2
  · have hbytes : encodeMovapsM128Xmm src am =
        am.rexByte false src :: 0x0F :: 0x29 :: am.modrm (regLow src) :: am.tail := ite_eq_right hlow
    have hlen : (encodeMovapsM128Xmm src am).length = 4 + am.tail.length := by
      rw [hbytes]; simp; omega
    obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movaps_m128_xmm_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv hx hb
    rw [hlen, hbytes]
    rwa [hr, gprNumber_reg] at this

/-! ### Through an FS/GS segment override -/

/-- The effect of `movaps r:[am], src` at `p` (an FS/GS override `r` whose segment has base
`base`), for an encoding of `len` bytes: the 16 bytes at `base + am.addr s (p + len)` set to the
XMM register `src`. -/
def movapsM128XmmSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + storeAddrAt p am len s)
    fun s => (Operand.xmm src : Operand 128).read s

@[simp] theorem movapsM128XmmSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (movapsM128XmmSegEffect p len base src am s).components =
      [.mem (base + storeAddrAt p am len s) 16, .rip] := by
  simp [movapsM128XmmSegEffect]

/-- The step behind `movaps_m128_xmm_seg_triple_of_bytes`. -/
theorem movaps_m128_xmm_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => SseAlignedStorePre p (4 + am.tail.length)
        (fun t => base + storeAddrAt p am (4 + am.tail.length) t) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (movapsM128XmmSegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am) :=
  StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => by
      obtain ⟨⟨⟨hp, hw, _⟩, hsse, halign⟩, hseg, hbase⟩ := hpre
      subst hp hbase
      have := am.tail_length_le
      exact movaps_m128_xmm_seg_step s h hsse r hseg reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) halign hw

/-- The triple for `movaps r:[am], xmm` behind an FS/GS prefix (`64`/`65 0F 29 /r`, `mod ≠ 3`) at
`p`, for `reg` 0–7 and a shape needing no REX bit: the precondition is `SseAlignedStorePre` at
`base + am.addr s (p + len)` plus the segment `r` ready with base `base`. -/
theorem movaps_m128_xmm_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => SseAlignedStorePre p (4 + am.tail.length)
        (fun t => base + storeAddrAt p am (4 + am.tail.length) t) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (Effect.post (movapsM128XmmSegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movaps_m128_xmm_seg_effect_step p r base reg am hv hx hb)

/-- The step behind `movaps_m128_xmm_rex_seg_triple_of_bytes`. -/
theorem movaps_m128_xmm_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SseAlignedStorePre p (5 + am.tail.length)
        (fun t => base + storeAddrAt p am (5 + am.tail.length) t) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (movapsM128XmmSegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  StepEffect.of_store_pre (n := 128) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => by
      obtain ⟨⟨⟨hp, hw, _⟩, hsse, halign⟩, hseg, hbase⟩ := hpre
      subst hp hbase
      have := am.tail_length_le
      exact movaps_m128_xmm_rex_seg_step s h hsse r hseg rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) halign hw

/-- The triple for `movaps r:[am], xmm` behind an FS/GS prefix and a REX prefix
(`64`/`65 rex 0F 29 /r`, `mod ≠ 3`) at `p`: any source register and shape. -/
theorem movaps_m128_xmm_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SseAlignedStorePre p (5 + am.tail.length)
        (fun t => base + storeAddrAt p am (5 + am.tail.length) t) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x29 :: am.modrm reg :: am.tail))
      (Effect.post (movapsM128XmmSegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movaps_m128_xmm_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

/-- The triple for `movaps r:[am], src` on the XMM register numbered `src` (0–15) at `p`, in the
encoding `r.prefixByte :: encodeMovapsM128Xmm src am`. -/
theorem movaps_m128_xmm_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SseAlignedStorePre p (r.prefixByte :: encodeMovapsM128Xmm src am).length
        (fun t => base + storeAddrAt p am (r.prefixByte :: encodeMovapsM128Xmm src am).length t) s ∧
        r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovapsM128Xmm src am))
      (Effect.post (movapsM128XmmSegEffect p (r.prefixByte :: encodeMovapsM128Xmm src am).length
        base (src.setWidth 5) am)) := by
  by_cases hlow : am.NoRex src
  · have hbytes : encodeMovapsM128Xmm src am = 0x0F :: 0x29 :: am.modrm (regLow src) :: am.tail :=
      ite_eq_left hlow
    have hlen : (r.prefixByte :: encodeMovapsM128Xmm src am).length = 4 + am.tail.length := by
      rw [hbytes]; simp; omega
    rw [hlen, hbytes, ← gprNumber_reg src, hlow.1]
    exact movaps_m128_xmm_seg_triple_of_bytes p r base (regLow src) am hv hlow.2.1 hlow.2.2
  · have hbytes : encodeMovapsM128Xmm src am =
        am.rexByte false src :: 0x0F :: 0x29 :: am.modrm (regLow src) :: am.tail := ite_eq_right hlow
    have hlen : (r.prefixByte :: encodeMovapsM128Xmm src am).length = 5 + am.tail.length := by
      rw [hbytes]; simp; omega
    obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movaps_m128_xmm_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hlen, hbytes]
    rwa [hr, gprNumber_reg] at this

/-! ### Examples -/

/-- `movaps [rsp + 0x10], xmm0` (`0F 29 44 24 10`). -/
example : encodeMovapsM128Xmm 0 (.sib 4 none 0 (.d8 0x10)) = [0x0F, 0x29, 0x44, 0x24, 0x10] := by
  decide
/-- `movaps [rsp + 0x20], xmm1` (`0F 29 4C 24 20`). -/
example : encodeMovapsM128Xmm 1 (.sib 4 none 0 (.d8 0x20)) = [0x0F, 0x29, 0x4C, 0x24, 0x20] := by
  decide
/-- `movaps [rsp + 0xD0], xmm0` (`0F 29 84 24 D0 00 00 00`). -/
example : encodeMovapsM128Xmm 0 (.sib 4 none 0 (.d32 0xD0)) =
    [0x0F, 0x29, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] := by decide
/-- `movaps [rsp + 0x80], xmm1` (`0F 29 8C 24 80 00 00 00`). -/
example : encodeMovapsM128Xmm 1 (.sib 4 none 0 (.d32 0x80)) =
    [0x0F, 0x29, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] := by decide
/-- `movaps [rsp + rcx + 0x10], xmm0` (`0F 29 44 0C 10`). -/
example : encodeMovapsM128Xmm 0 (.sib 4 (some 1) 0 (.d8 0x10)) = [0x0F, 0x29, 0x44, 0x0C, 0x10] := by
  decide
/-- `movaps [rsp + rcx + 0x20], xmm1` (`0F 29 4C 0C 20`). -/
example : encodeMovapsM128Xmm 1 (.sib 4 (some 1) 0 (.d8 0x20)) = [0x0F, 0x29, 0x4C, 0x0C, 0x20] := by
  decide
/-- A REX encoding: `movaps [r8 + 0x10], xmm9` (`45 0F 29 48 10`). -/
example : encodeMovapsM128Xmm 9 (.base 8 (.d8 0x10)) = [0x45, 0x0F, 0x29, 0x48, 0x10] := by decide

/-- `movaps [rsp + 0x10], xmm0` at `p`, as a triple on its literal bytes. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseAlignedStorePre p 5 (storeAddrAt p (.sib 4 none 0 (.d8 0x10)) 5))
      (codeRange p [0x0F, 0x29, 0x44, 0x24, 0x10])
      (Effect.post (movapsM128XmmEffect p 5 0 (.sib 4 none 0 (.d8 0x10)))) :=
  movaps_m128_xmm_triple_of_bytes p 0 (.sib 4 none 0 (.d8 0x10)) ⟨by decide, by decide⟩ rfl rfl

/-- `movaps [rsp + 0xC0], xmm1` at `p` (`0F 29 8C 24 C0 00 00 00`). -/
example [Bindings] (p : BitVec 64) :
    Triple (SseAlignedStorePre p 8 (storeAddrAt p (.sib 4 none 0 (.d32 0xC0)) 8))
      (codeRange p [0x0F, 0x29, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00])
      (Effect.post (movapsM128XmmEffect p 8 1 (.sib 4 none 0 (.d32 0xC0)))) :=
  movaps_m128_xmm_triple_of_bytes p 1 (.sib 4 none 0 (.d32 0xC0)) ⟨by decide, by decide⟩ rfl rfl

/-- `movaps [rsp + rcx + 0x20], xmm1` at `p` (`0F 29 4C 0C 20`). -/
example [Bindings] (p : BitVec 64) :
    Triple (SseAlignedStorePre p 5 (storeAddrAt p (.sib 4 (some 1) 0 (.d8 0x20)) 5))
      (codeRange p [0x0F, 0x29, 0x4C, 0x0C, 0x20])
      (Effect.post (movapsM128XmmEffect p 5 1 (.sib 4 (some 1) 0 (.d8 0x20)))) :=
  movaps_m128_xmm_triple_of_bytes p 1 (.sib 4 (some 1) 0 (.d8 0x20)) ⟨by decide, by decide⟩ rfl rfl
attribute [x86_compose] movapsM128XmmEffect

@[x86_local] theorem movapsM128XmmEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movapsM128XmmEffect p len src am) := by
  effect_local [movapsM128XmmEffect, storeEffect]

attribute [x86_compose] movapsM128XmmSegEffect

@[x86_local] theorem movapsM128XmmSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movapsM128XmmSegEffect p len base src am) := by
  effect_local [movapsM128XmmSegEffect, storeEffect]

end X86Proofs
