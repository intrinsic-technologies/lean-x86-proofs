import X86Proofs.Step.FetchImm
import X86Proofs.Step.Memory
import X86Proofs.Step.Decode
import X86Proofs.Step.Prefix

/-!
# Memory operand addresses: ModRM, SIB and displacement

A memory operand's address in 64-bit mode, as lean-x86's `Effective_Address` computes it from the
ModRM `mod` and `rm` fields, an optional SIB byte and a displacement, and how the decoder fetches
those bytes: at address size 64, and at address size 32 (a `67` prefix; `AddrMode.addr32`).

- `Disp`: the displacement and its encoded width (none, 8 or 32 bits). The width is part of the
  encoding (`nopw 0x0(%rax,%rax,1)` has a 32-bit zero), so it is explicit.
- `AddrMode`: an addressing shape with its registers and displacement: `[base + disp]` without a
  SIB byte, `[base + index * 2^scale + disp]` with one (the index may be absent, as for
  `[rsp + disp]`), `[rip + disp32]`, or `[index * 2^scale + disp32]` with no base (`.abs`; with
  no index the absolute `[disp32]`, as in `fs:[0x28]`).
- `AddrMode.modrm reg`, `AddrMode.tail` (SIB and displacement bytes), `AddrMode.rexB` /
  `AddrMode.rexX`: the encoding. An instruction with a memory operand is `prefixes, opcode,
  am.modrm reg, am.tail, immediate`.
- `AddrMode.addr am s next`: the address, a function of the registers of `s` (and, for
  RIP-relative operands, of `next`, the address of the byte after the displacement):
  `base + (index <<< scale) + signExtend disp`, wrapping at 2^64.
- `AddrMode.addr32 am s next`: the address at address size 32 (a `67` prefix): the 32-bit sum
  `base32 + index32 * 2^scale + disp` (EIP-relative for `.rip`), zero-extended, i.e. `addr`'s low
  32 bits (`addrAt32` at the instruction's end; `offset32`: what `Effective_Address` returns
  before `Handle_RIP_Relative_Address` truncates it).
- `AddrMode.Valid`: the shape is encodable (no SIB-only `rm` without a SIB byte, no index RSP, no
  `mod = 0` with a base whose low bits are `101`, which would mean "no base").
- `AddrContext ctx am`: the decode context facts the computation reads: no segment prefix, 64-bit
  mode, REX.B/REX.X as `am` needs, no REX2 bits. `SegAddrContext ctx am`: the same with any
  segment prefix, whose segment must be ready for data accesses (`SegReady`).

The lemmas:

- `effectiveAddress_run_seg`: `Effective_Address` with `am.mod` and `am.rm`, run where the decoder
  runs it (`k` byte fetches done, `am.tail` stored at offset `i` of the instruction at RIP),
  fetches exactly `am.tail` and returns `AddrMode.offset` (the address, or for RIP-relative
  operands the displacement), the segment `ctxSegment ctx am.isStack` (FS or GS after a segment
  prefix, else the flat data segment `flatData am.isStack`: SS for a base RSP or RBP, else DS;
  both have base 0), the address after the displacement, whether the operand is
  RIP-relative, and whether its base is RSP (`AddrMode.baseUsesRsp`, which only `POP m` reads).
  `effectiveAddress_run`: the same without a segment prefix (`AddrContext`), the segment
  `flatData am.isStack`.
- `handleRIPRelativeAddress_addrMode_run`: lean-x86's `Handle_RIP_Relative_Address` then gives `am.addr`.
- `effectiveAddress32_run_seg`, `handleRIPRelativeAddress_addrMode32_run`: the same at address
  size 32, returning `am.offset32` and then `am.addr32`
  (`handleRIPRelativeAddress_addrMode32_add_run` with an offset added first, as BT does).
- `AddrMode.reg64_write_rsp_of_ne`, `AddrMode.reg64_write_rsp_self`, `AddrMode.addr_write_rsp_add`:
  an RSP write leaves the other registers alone and moves an address by the same amount exactly
  when its base is RSP, which `POP m` relies on.
- `directMemoryOffset_run`: `Direct_Memory_Offset` (the `moffs` operand of `A0`–`A3`) fetches the
  8-byte absolute offset and returns it with the flat data segment (`MoffsContext`: the context
  facts it reads); `directMemoryOffset_run_seg`: the same with any segment prefix (`SegMoffsContext`;
  the segment is `ctxSegment ctx false`); `directMemoryOffset32_run_seg` (`SegMoffsContext32`),
  `handleRIPRelativeAddress32_zext_run`: at address size 32, a 4-byte offset, zero-extended.

Segments: in 64-bit mode lean-x86 replaces the segment by a null segment of the same kind
(`Get_Effective_Segment` → `Null_Segment`) unless there is a segment prefix, so DS, ES and SS all
have base 0 once `SupportedIntegerCPU` (in `ReadyToStep`) fixes them; FS and GS (whose bases are
not 0) are reached only by a segment prefix (`64`, `65`: `seg_prefix_present`; `2E` does not
count in 64-bit mode), which `Get_Effective_Segment` returns as is (`effSegment`). The internal
lemmas (`readSIB_run`, `effectiveAddress_base_run`, …) return `effSegment ctx` of the default
segment, for any prefix.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers
open scoped X86.Runtime.Syntax

/-! ### Addressing shapes and their encoding -/

/-- A displacement with its encoded width. -/
inductive Disp where
  /-- No displacement (`mod = 00`). -/
  | none
  /-- An 8-bit displacement, sign-extended (`mod = 01`). -/
  | d8 (v : BitVec 8)
  /-- A 32-bit displacement, sign-extended (`mod = 10`). -/
  | d32 (v : BitVec 32)
  deriving DecidableEq

namespace Disp

/-- The ModRM `mod` field for this displacement. -/
def mod : Disp → BitVec 2
  | .none => 0
  | .d8 _ => 1
  | .d32 _ => 2

/-- The displacement's bytes, little-endian. -/
def bytes : Disp → List UInt8
  | .none => []
  | .d8 v => immBytes 8 v
  | .d32 v => immBytes 32 v

/-- The displacement, sign-extended to 64 bits. -/
def value : Disp → BitVec 64
  | .none => 0
  | .d8 v => v.signExtend 64
  | .d32 v => v.signExtend 64

theorem mod_bne_three (d : Disp) : (d.mod != 3) = true := by cases d <;> rfl

@[simp] theorem bytes_length_le (d : Disp) : d.bytes.length ≤ 4 := by
  cases d <;> simp [bytes]

/-! The displacement's length for each width. -/

theorem bytes_length_none : Disp.none.bytes.length = 0 := by simp [bytes]

theorem bytes_length_d8 (v : BitVec 8) : (Disp.d8 v).bytes.length = 1 := by
  simp [bytes, immBytes]

theorem bytes_length_d32 (v : BitVec 32) : (Disp.d32 v).bytes.length = 4 := by
  simp [bytes, immBytes]

end Disp

/-- A memory operand's addressing shape, with its registers (numbers 0–15) and displacement. -/
inductive AddrMode where
  /-- `[b + disp]` without a SIB byte (`rm = b & 7`, which must not be `100`). -/
  | base (b : BitVec 4) (disp : Disp)
  /-- `[b + index * 2^scale + disp]` with a SIB byte (`rm = 100`); `index = none` is the SIB
  index field `100` without REX.X (no index), as in `[rsp + disp]`. -/
  | sib (b : BitVec 4) (index : Option (BitVec 4)) (scale : BitVec 2) (disp : Disp)
  /-- `[rip + disp32]` (`mod = 00`, `rm = 101`): relative to the address after the
  displacement. -/
  | rip (disp : BitVec 32)
  /-- `[index * 2^scale + disp32]` with no base: a SIB byte with base field `101` and `mod = 00`
  (`index = none`: index field `100`, the absolute address `[disp32]`, as in `fs:[0x28]`). -/
  | abs (index : Option (BitVec 4)) (scale : BitVec 2) (disp : BitVec 32)
  deriving DecidableEq

/-- The low three bits of a register number (the ModRM/SIB field). -/
def regLow (r : BitVec 4) : BitVec 3 := r.extractLsb' 0 3

/-- The top bit of a register number (the REX bit). -/
def regHigh (r : BitVec 4) : BitVec 1 := r.extractLsb' 3 1

/-- The SIB index field's REX bit: the top bit of the index register, 0 if there is none. -/
def idxHigh : Option (BitVec 4) → BitVec 1
  | some i => regHigh i
  | none => 0

/-- The SIB index field: the low bits of the index register, `100` if there is none. -/
def idxLow : Option (BitVec 4) → BitVec 3
  | some i => regLow i
  | none => 4

namespace AddrMode

/-- The shape is encodable: a no-SIB base is not RSP/R12 (`rm = 100` means SIB), RSP is not an
index (index field `100` without REX.X means none), and without a displacement the base is not
RBP/R13 (`mod = 00` with base `101` means no base). -/
def Valid : AddrMode → Prop
  | .base b d => regLow b ≠ 4 ∧ (d = .none → regLow b ≠ 5)
  | .sib b i _ d => i ≠ some 4 ∧ (d = .none → regLow b ≠ 5)
  | .rip _ => True
  | .abs i _ _ => i ≠ some 4

/-- The ModRM `mod` field. -/
def mod : AddrMode → BitVec 2
  | .base _ d => d.mod
  | .sib _ _ _ d => d.mod
  | .rip _ => 0
  | .abs .. => 0

/-- The ModRM `rm` field. -/
def rm : AddrMode → BitVec 3
  | .base b _ => regLow b
  | .sib .. => 4
  | .rip _ => 5
  | .abs .. => 4

/-- The REX.B bit the shape needs (top bit of the base). -/
def rexB : AddrMode → BitVec 1
  | .base b _ => regHigh b
  | .sib b _ _ _ => regHigh b
  | .rip _ => 0
  | .abs .. => 0

/-- The REX.X bit the shape needs (top bit of the index). -/
def rexX : AddrMode → BitVec 1
  | .sib _ i _ _ => idxHigh i
  | .abs i _ _ => idxHigh i
  | _ => 0

/-- The REX byte of an instruction whose ModRM `reg` field names register `reg` (0–15) and whose
memory operand is `am`: W = `w`, R = top bit of `reg`, X and B as `am` needs. -/
def rexByte (am : AddrMode) (w : Bool) (reg : BitVec 4) : UInt8 :=
  UInt8.ofNat (0x40 + 8 * w.toNat + 4 * (regHigh reg).toNat + 2 * am.rexX.toNat + am.rexB.toNat)

/-- The instruction needs no REX prefix: register `reg` is 0–7 and `am` needs no REX bit. -/
abbrev NoRex (am : AddrMode) (reg : BitVec 4) : Prop :=
  regHigh reg = 0 ∧ am.rexX = 0 ∧ am.rexB = 0

/-- The SIB byte: `scale`, index field, base field. -/
def sibByte (b : BitVec 4) (i : Option (BitVec 4)) (scale : BitVec 2) : UInt8 :=
  UInt8.ofBitVec (scale ++ idxLow i ++ regLow b)

/-- The ModRM byte with `reg` field `reg`. -/
def modrm (am : AddrMode) (reg : BitVec 3) : UInt8 := UInt8.ofBitVec (am.mod ++ reg ++ am.rm)

/-- The bytes after the ModRM byte: the SIB byte (if any) and the displacement. -/
def tail : AddrMode → List UInt8
  | .base _ d => d.bytes
  | .sib b i sc d => sibByte b i sc :: d.bytes
  | .rip d => immBytes 32 d
  | .abs i sc d => sibByte 5 i sc :: immBytes 32 d

/-- The access goes through SS (base RBP without SIB; base RSP or RBP with SIB) rather than DS.
In 64-bit mode both have base 0, so this only selects which flat segment lean-x86 uses. -/
def isStack : AddrMode → Bool
  | .base b _ => b == 5
  | .sib b _ _ _ => b == 4 || b == 5
  | .rip _ => false
  | .abs .. => false

/-- The operand is RIP-relative. -/
def isRip : AddrMode → Bool
  | .rip _ => true
  | _ => false

/-- The base register is RSP (SIB base `100` without REX.B), which `Effective_Address` reports
(`base_uses_rsp`): `POP m` adds the popped size to such an address. -/
def baseUsesRsp : AddrMode → Bool
  | .sib b _ _ _ => b == 4
  | _ => false

/-- The 64-bit value of register number `r`. -/
def reg64 (r : BitVec 4) (s : RamState) : BitVec 64 :=
  (Operand.reg (r.setWidth 5) : Operand 64).read s

/-- The address of the operand in state `s`: `base + (index <<< scale) + disp`, or for a
RIP-relative operand `next + disp`, where `next` is the address after the displacement (the end
of the instruction if no immediate follows). Wraps at 2^64. -/
def addr (am : AddrMode) (s : RamState) (next : BitVec 64) : BitVec 64 :=
  match am with
  | .base b d => reg64 b s + d.value
  | .sib b none _ d => reg64 b s + d.value
  | .sib b (some i) sc d => reg64 b s + (reg64 i s <<< sc.toNat) + d.value
  | .rip d => next + d.signExtend 64
  | .abs none _ d => d.signExtend 64
  | .abs (some i) sc d => (reg64 i s <<< sc.toNat) + d.signExtend 64

/-- The operand's address in state `s` for an instruction of `len` bytes at RIP: `addr` with the
instruction's end, RIP + `len`, as the RIP-relative base. -/
abbrev addrAt (am : AddrMode) (s : RamState) (len : Nat) : BitVec 64 :=
  am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 len))

/-- What `Effective_Address` returns as the offset: the address, except that a RIP-relative
operand's RIP is added afterwards (`Handle_RIP_Relative_Address`). -/
def offset (am : AddrMode) (s : RamState) : BitVec 64 :=
  match am with
  | .rip d => d.signExtend 64
  | am => am.addr s 0

/-- The operand's address with an address-size prefix (`67`, address size 32): the 32-bit sum
`base32 + index32 * 2^scale + disp` (for a RIP-relative operand `next + disp`, EIP-relative),
zero-extended to 64 bits. It is `addr`'s low 32 bits, zero-extended, since those depend only on the
registers' low 32 bits. -/
def addr32 (am : AddrMode) (s : RamState) (next : BitVec 64) : BitVec 64 :=
  ((am.addr s next).setWidth 32).setWidth 64

/-- `addr32` for an instruction of `len` bytes at RIP (`addrAt` at address size 32). -/
abbrev addrAt32 (am : AddrMode) (s : RamState) (len : Nat) : BitVec 64 :=
  am.addr32 s (BitVec.add s.RIP (BitVec.ofNat 64 len))

/-- What `Effective_Address` returns as the offset at address size 32: `offset`, except that a
base without a SIB byte is read as its low 32 bits, sign-extended. `Handle_RIP_Relative_Address`
then keeps the low 32 bits (`handleRIPRelativeAddress_addrMode32_run`). -/
def offset32 (am : AddrMode) (s : RamState) : BitVec 64 :=
  match am with
  | .base b d => ((reg64 b s).setWidth 32).signExtend 64 + d.value
  | am => am.offset s

@[simp] theorem tail_length_le (am : AddrMode) : am.tail.length ≤ 5 := by
  cases am with
  | base b d => cases d <;> simp [tail, Disp.bytes]
  | sib b i sc d => cases d <;> simp [tail, Disp.bytes]
  | rip d => simp [tail]
  | abs i sc d => simp [tail]

/-! The SIB and displacement bytes' length for each shape. -/

theorem tail_length_base (b : BitVec 4) (d : Disp) :
    (AddrMode.base b d).tail.length = d.bytes.length := by
  simp [tail]

theorem tail_length_sib (b : BitVec 4) (sc : BitVec 2) (o : Option (BitVec 4)) (d : Disp) :
    (AddrMode.sib b o sc d).tail.length = d.bytes.length + 1 := by
  simp [tail]

theorem tail_length_rip (v : BitVec 32) : (AddrMode.rip v).tail.length = 4 := by
  simp [tail, immBytes]

theorem tail_length_abs (sc : BitVec 2) (v : BitVec 32) (o : Option (BitVec 4)) :
    (AddrMode.abs o sc v).tail.length = 5 := by
  simp [tail, immBytes]

/-- The address depends only on the general-purpose registers. -/
theorem addr_of_gpr {am : AddrMode} {s t : RamState} (h : t.GPR = s.GPR) (next : BitVec 64) :
    am.addr t next = am.addr s next := by
  cases am with
  | base b d => simp [addr, reg64, Operand.read, h]
  | sib b i sc d => cases i <;> simp [addr, reg64, Operand.read, h]
  | rip d => rfl
  | abs i sc d => cases i <;> simp [addr, reg64, Operand.read, h]

/-- The 32-bit address depends only on the general-purpose registers. -/
theorem addr32_of_gpr {am : AddrMode} {s t : RamState} (h : t.GPR = s.GPR) (next : BitVec 64) :
    am.addr32 t next = am.addr32 s next := by
  simp only [addr32, addr_of_gpr h]

/-- `rexByte` with W = 1 is a REX.W prefix with the R, X and B bits it was built from. -/
theorem rexByte_true_spec (am : AddrMode) (reg : BitVec 4) :
    RexWPrefix (am.rexByte true reg).toBitVec ∧ rexR (am.rexByte true reg).toBitVec = regHigh reg ∧
      X86Proofs.rexX (am.rexByte true reg).toBitVec = am.rexX ∧
      X86Proofs.rexB (am.rexByte true reg).toBitVec = am.rexB := by
  unfold rexByte
  generalize am.rexX = x
  generalize am.rexB = b
  unfold RexWPrefix
  revert reg x b
  decide

/-- `rexByte` with W = 0 is a REX prefix with W = 0 and the R, X and B bits it was built from. -/
theorem rexByte_false_spec (am : AddrMode) (reg : BitVec 4) :
    RexNoWPrefix (am.rexByte false reg).toBitVec ∧
      rexR (am.rexByte false reg).toBitVec = regHigh reg ∧
      X86Proofs.rexX (am.rexByte false reg).toBitVec = am.rexX ∧
      X86Proofs.rexB (am.rexByte false reg).toBitVec = am.rexB := by
  unfold rexByte
  generalize am.rexX = x
  generalize am.rexB = b
  unfold RexNoWPrefix
  revert reg x b
  decide

end AddrMode

/-- A register other than RSP holds the same value after RSP is written. -/
theorem AddrMode.reg64_write_rsp_of_ne (r : BitVec 4) (hr : r ≠ 4) (s : RamState) (v : BitVec 64) :
    AddrMode.reg64 r ((Operand.reg 4 : Operand 64).write s v) = AddrMode.reg64 r s := by
  have hne : (4 : BitVec 5) ≠ r.setWidth 5 := by
    revert r; decide
  exact Operand.read_write_reg_of_ne (m := 64) s hne v

/-- RSP after it is written. -/
theorem AddrMode.reg64_write_rsp_self (s : RamState) (v : BitVec 64) :
    AddrMode.reg64 4 ((Operand.reg 4 : Operand 64).write s v) = v := by
  simp [AddrMode.reg64]

/-- Writing `RSP + k` to RSP adds `k` to the address exactly when its base is RSP (`baseUsesRsp`). -/
theorem AddrMode.addr_write_rsp_add (am : AddrMode) (hv : am.Valid) (k : BitVec 64) (next : BitVec 64)
    (s : RamState) :
    am.addr ((Operand.reg 4 : Operand 64).write s (AddrMode.reg64 4 s + k)) next =
      if am.baseUsesRsp then am.addr s next + k else am.addr s next := by
  have h4 : ∀ b : BitVec 4, regLow b ≠ 4 → b ≠ 4 := by decide
  cases am with
  | base b d =>
    simp only [AddrMode.baseUsesRsp, Bool.false_eq_true, ↓reduceIte, AddrMode.addr,
      AddrMode.reg64_write_rsp_of_ne b (h4 b hv.1)]
  | sib b i sc d =>
    have hi : ∀ j, i = some j → j ≠ 4 := fun j hj h => hv.1 (h ▸ hj)
    by_cases hb : b = 4
    · subst hb
      cases i with
      | none =>
        simp only [AddrMode.baseUsesRsp, beq_self_eq_true, ↓reduceIte, AddrMode.addr,
          AddrMode.reg64_write_rsp_self]
        ac_rfl
      | some j =>
        simp only [AddrMode.baseUsesRsp, beq_self_eq_true, ↓reduceIte, AddrMode.addr,
          AddrMode.reg64_write_rsp_self, AddrMode.reg64_write_rsp_of_ne j (hi j rfl)]
        ac_rfl
    · have hb' : (b == 4) = false := by simpa using hb
      cases i with
      | none =>
        simp only [AddrMode.baseUsesRsp, hb', Bool.false_eq_true, ↓reduceIte, AddrMode.addr,
          AddrMode.reg64_write_rsp_of_ne b hb]
      | some j =>
        simp only [AddrMode.baseUsesRsp, hb', Bool.false_eq_true, ↓reduceIte, AddrMode.addr,
          AddrMode.reg64_write_rsp_of_ne b hb, AddrMode.reg64_write_rsp_of_ne j (hi j rfl)]
  | rip d => rfl
  | abs i sc d =>
    cases i with
    | none => rfl
    | some j =>
      have hj : j ≠ 4 := fun h => hv (h ▸ rfl)
      simp only [AddrMode.baseUsesRsp, Bool.false_eq_true, ↓reduceIte, AddrMode.addr,
        AddrMode.reg64_write_rsp_of_ne j hj]

/-- The decode-context facts the address computation reads: no segment prefix, 64-bit mode, no
REX2 bits, and REX.B and REX.X as the shape needs. -/
structure AddrContext (ctx : Instruction_Context) (am : AddrMode) : Prop where
  seg : ctx.seg_prefix_present = false
  mode64 : ctx.is_mode64 = true
  b4 : ctx.rex_b4 = 0
  x4 : ctx.rex_x4 = 0
  b3 : ctx.rex_b3 = am.rexB
  x3 : ctx.rex_x3 = am.rexX

/-- The decode context without a prefix gives what the address computation reads, if the shape
needs neither REX.X nor REX.B. -/
theorem AddrContext.legacy (seg : X86.Helpers.Segment) (am : AddrMode) (hx : am.rexX = 0)
    (hb : am.rexB = 0) : AddrContext (legacyContext seg) am :=
  ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩

/-- The decode-context facts the address computation reads when the operand may have a segment
override: 64-bit mode, no REX2 bits, REX.B and REX.X as the shape needs, and, if there is a
segment prefix (FS or GS), its segment is ready for data accesses (`SegReady`). The access then
goes through `ctxSegment ctx` at `segAddr ctx` (`SegAccess.ctx`). -/
structure SegAddrContext (ctx : Instruction_Context) (am : AddrMode) : Prop where
  seg : ctx.seg_prefix_present = true → SegReady ctx.segment
  mode64 : ctx.is_mode64 = true
  b4 : ctx.rex_b4 = 0
  x4 : ctx.rex_x4 = 0
  b3 : ctx.rex_b3 = am.rexB
  x3 : ctx.rex_x3 = am.rexX

/-- Without a segment prefix, `AddrContext` gives `SegAddrContext`. -/
theorem AddrContext.toSeg {ctx : Instruction_Context} {am : AddrMode} (h : AddrContext ctx am) :
    SegAddrContext ctx am :=
  ⟨fun hs => absurd (h.seg.symm.trans hs) Bool.false_ne_true, h.mode64, h.b4, h.x4, h.b3, h.x3⟩

/-! ### ModRM and SIB fields -/

theorem append_hi (m : BitVec 2) (r x : BitVec 3) : (m ++ r ++ x).extractLsb' 6 2 = m := by
  revert m r x; decide

theorem append_mid (m : BitVec 2) (r x : BitVec 3) : (m ++ r ++ x).extractLsb' 3 3 = r := by
  revert m r x; decide

theorem append_lo (m : BitVec 2) (r x : BitVec 3) : (m ++ r ++ x).extractLsb' 0 3 = x := by
  revert m r x; decide

@[simp] theorem AddrMode.modrmMod_modrm (am : AddrMode) (reg : BitVec 3) :
    modrmMod (am.modrm reg) = am.mod := append_hi _ _ _

@[simp] theorem AddrMode.modrmReg_modrm (am : AddrMode) (reg : BitVec 3) :
    modrmReg (am.modrm reg) = reg := append_mid _ _ _

@[simp] theorem AddrMode.modrmRm_modrm (am : AddrMode) (reg : BitVec 3) :
    modrmRm (am.modrm reg) = am.rm := append_lo _ _ _

theorem AddrMode.mod_ne_three (am : AddrMode) : am.mod ≠ 3 := by
  cases am with
  | base b d => cases d <;> simp [mod, Disp.mod] <;> decide
  | sib b i sc d => cases d <;> simp [mod, Disp.mod] <;> decide
  | rip d => simp [mod]
  | abs i sc d => simp [mod]

theorem sibByte_toBitVec (b : BitVec 4) (i : Option (BitVec 4)) (sc : BitVec 2) :
    (AddrMode.sibByte b i sc).toBitVec = sc ++ idxLow i ++ regLow b := rfl

/-- A register number from its REX bit and low bits. -/
theorem gprNumber_reg (r : BitVec 4) : gprNumber 0 (regHigh r) (regLow r) = r.setWidth 5 := by
  revert r; decide

/-! ### lean-x86's building blocks -/

theorem concatBits_reg4 {ε σ : Type} (b : BitVec 4) :
    (X86.Runtime.concatBits (leftSize := 1) (rightSize := 3) (regHigh b) (regLow b) :
      X86.Runtime.SpecM ε σ (X86.Runtime.Bits (1 + 3))) =
      (pure b : X86.Runtime.SpecM ε σ (BitVec 4)) := by
  have : ∀ b : BitVec 4, BitVec.ofNat 4 ((regHigh b).toNat <<< 3 + (regLow b).toNat) = b := by
    decide
  simp only [x86_runtime]
  exact congrArg (fun x => (pure x : X86.Runtime.SpecM ε σ _)) (this b)

theorem concatBits_hi2 {ε σ : Type} (h : BitVec 1) :
    (X86.Runtime.concatBits (leftSize := 1) (rightSize := 1) (0 : BitVec 1) h :
      X86.Runtime.SpecM ε σ (X86.Runtime.Bits (1 + 1))) =
      (pure (h.setWidth 2) : X86.Runtime.SpecM ε σ (BitVec 2)) := by
  have : ∀ h : BitVec 1, BitVec.ofNat 2 ((0 : BitVec 1).toNat <<< 1 + h.toNat) = h.setWidth 2 := by
    decide
  simp only [x86_runtime]
  exact congrArg (fun x => (pure x : X86.Runtime.SpecM ε σ _)) (this h)

theorem concatBits_reg5 {ε σ : Type} (b : BitVec 4) :
    (X86.Runtime.concatBits (leftSize := 2) (rightSize := 3) ((regHigh b).setWidth 2) (regLow b) :
      X86.Runtime.SpecM ε σ (X86.Runtime.Bits (2 + 3))) =
      (pure (b.setWidth 5) : X86.Runtime.SpecM ε σ (BitVec 5)) := by
  have : ∀ b : BitVec 4,
      BitVec.ofNat 5 (((regHigh b).setWidth 2).toNat <<< 3 + (regLow b).toNat) = b.setWidth 5 := by
    decide
  simp only [x86_runtime]
  exact congrArg (fun x => (pure x : X86.Runtime.SpecM ε σ _)) (this b)

theorem concatBits_none5 {ε σ : Type} :
    (X86.Runtime.concatBits (leftSize := 2) (rightSize := 3) ((0 : BitVec 1).setWidth 2)
      (4 : BitVec 3) : X86.Runtime.SpecM ε σ (X86.Runtime.Bits (2 + 3))) =
      (pure 4 : X86.Runtime.SpecM ε σ (BitVec 5)) := by
  simp only [x86_runtime]
  rfl

theorem exp2_scale (sc : BitVec 2) :
    Std.Integer.Exp 2 (X86.Runtime.Unsigned sc) = .ok ((2 ^ sc.toNat : Nat) : Int) := by
  rw [stdExp_two_eq_ok _ (by simp [x86_runtime])]
  simp [x86_runtime]

theorem setWidth5_stack (b : BitVec 4) :
    ((b.setWidth 5 == 4) || (b.setWidth 5 == 5)) = (b == 4 || b == 5) := by
  revert b; decide

theorem setWidth5_and7 (b : BitVec 4) : ((b.setWidth 5 &&& 7) == 5) = (regLow b == 5) := by
  revert b; decide

theorem setWidth5_ne4 (j : BitVec 4) (h : j ≠ 4) : (j.setWidth 5 == 4) = false := by
  revert j; decide

/-- Register number `b` as lean-x86's 5-bit number is RSP's exactly when `b` is 4
(`base_uses_rsp`; the literal is at lean-x86's type `Bits 5`, as the generated code has it). -/
theorem setWidth5_beq4 (b : BitVec 4) :
    ((b.setWidth 5 : X86.Runtime.Bits 5) == (4 : X86.Runtime.Bits 5)) = (b == 4) := by
  revert b; decide

/-- A base register without a SIB byte (ModRM `rm` is not `100`) is not RSP. -/
theorem setWidth5_beq4_of_regLow (b : BitVec 4) (h : (regLow b == 4) = false) :
    ((b.setWidth 5 : X86.Runtime.Bits 5) == (4 : X86.Runtime.Bits 5)) = false := by
  revert b; decide

theorem mul_pow_shift (x : BitVec 64) (n : Nat) :
    x * BitVec.ofInt 64 ((2 ^ n : Nat) : Int) = x <<< n := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_natCast]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow]

theorem nullDataSegment_idem (seg : Segment) :
    nullDataSegment (nullDataSegment seg) = nullDataSegment seg := rfl

/-- The flat segment a 64-bit data access goes through, from SS or DS. -/
theorem nullDataSegment_stack (s : RamState) (hds : s.DS = {userStackSegment with is_stack := some false})
    (hss : s.SS = userStackSegment) (b : Bool) :
    nullDataSegment (if b = true then s.SS else s.DS) = flatData b := by
  cases b <;> simp [hds, hss] <;> rfl

/-- `get`, as a lemma for `spec_run`: stepping over `get` by `rfl` leaves the kernel to rediscover
the state, which can be very slow, so the address lemmas give it explicitly. -/
theorem get_run (t : RamState) :
    (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t = (.ok t, t) := rfl

/-! ### `Effective_Address`, given the fetches -/

/-- The displacement `d` is fetched at `ip`, from `s` to `t` (nothing for `none`). -/
def Disp.Fetched [Bindings] (d : Disp) (ip : BitVec 64) (s t : RamState) : Prop :=
  match d with
  | .none => t = s
  | .d8 v => (Mem_Fetch ip 8).run s = (.ok v, t)
  | .d32 v => (Mem_Fetch ip 32).run s = (.ok v, t)

/-- `Read_SIB` with the SIB byte of `b`, `i`, `sc` and displacement `d`, given its fetches. -/
theorem readSIB_run [Bindings] (s t u : RamState) (ctx : Instruction_Context) (ip : BitVec 64)
    (b : BitVec 4) (i : Option (BitVec 4)) (sc : BitVec 2) (d : Disp)
    (hi4 : i ≠ some 4) (h5 : d = .none → regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0) (hx3 : ctx.rex_x3 = idxHigh i)
    (hx4 : ctx.rex_x4 = 0) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte b i sc).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : d.Fetched (ip + 1) t u) :
    (Read_SIB ctx d.mod 1 ip).run s =
      (.ok (effSegment ctx (if (b == 4 || b == 5) = true then t.SS else t.DS),
        AddrMode.reg64 b t + d.value,
        (match i with | some j => AddrMode.reg64 j t | none => 0),
        ((2 ^ sc.toNat : Nat) : Int), ip + BitVec.ofNat 64 (1 + d.bytes.length), b == 4), u) := by
  unfold Read_SIB
  refine (specM_bind_run _ _ hsib).trans ?_
  simp (config := { decide := true }) only [sliceInclusive_eq,
    X86.Runtime.CheckedSlice.read, slice_eq_pure, pure_bind, Int.reduceToNat, Int.reduceSub,
    Int.reduceAdd, sibByte_toBitVec, append_hi, append_mid, append_lo, exp2_scale, hb3, hb4, hx3,
    hx4, concatBits_hi2, concatBits_reg5, HOr.hOr, OrOp.or, strictOr,
    getEffectiveSegment_run_eff ctx _ hm64]
  have hfin : ∀ (x : BitVec 64), x * BitVec.ofInt 64 1 = x := fun x => BitVec.mul_one x
  have hz : ∀ (x : BitVec 64), x + 0 = x := fun x => BitVec.add_zero x
  cases i with
  | none =>
    simp (config := { decide := true }) only [idxHigh, idxLow, concatBits_none5, pure_bind,
      ↓reduceIte]
    rw [setWidth5_stack]
    cases d with
    | none =>
      subst hdisp
      have h5 : (regLow b == 5) = false := by simpa using h5 rfl
      simp only [Disp.mod]
      rw [setWidth5_and7, h5]
      by_cases hst : (b == 4 || b == 5) = true <;>
      · simp only [hst, Bool.false_eq_true, ↓reduceIte]
        spec_run [Read_GPR => readGPR64_run _ _ hmode, MonadState.get => get_run _]
        simp only [Disp.value]
        rw [hz, setWidth5_beq4]
        simp [AddrMode.reg64, Operand.read, Disp.bytes]
    | d8 v =>
      by_cases hst : (b == 4 || b == 5) = true <;>
      · simp only [hst, Bool.false_eq_true, ↓reduceIte, Disp.mod]
        spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp, MonadState.get => get_run _]
        rw [setWidth5_beq4]
        simp [AddrMode.reg64, Operand.read, Disp.value, Disp.bytes, BitVec.signExtend]
    | d32 v =>
      by_cases hst : (b == 4 || b == 5) = true <;>
      · simp only [hst, Bool.false_eq_true, ↓reduceIte, Disp.mod]
        spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp, MonadState.get => get_run _]
        rw [setWidth5_beq4]
        simp [AddrMode.reg64, Operand.read, Disp.value, Disp.bytes, BitVec.add_assoc, BitVec.signExtend]
  | some j =>
    have hj : j ≠ 4 := fun h => hi4 (h ▸ rfl)
    simp (config := { decide := true }) only [idxHigh, idxLow, concatBits_reg5, pure_bind,
      ↓reduceIte, setWidth5_ne4 j hj]
    rw [setWidth5_stack]
    cases d with
    | none =>
      subst hdisp
      have h5 : (regLow b == 5) = false := by simpa using h5 rfl
      simp only [Disp.mod]
      rw [setWidth5_and7, h5]
      by_cases hst : (b == 4 || b == 5) = true <;>
      · simp only [hst, Bool.false_eq_true, ↓reduceIte]
        spec_run [Read_GPR => readGPR64_run _ _ hmode, MonadState.get => get_run _]
        simp only [Disp.value]
        rw [hz, setWidth5_beq4]
        simp [AddrMode.reg64, Operand.read, Disp.bytes]
    | d8 v =>
      by_cases hst : (b == 4 || b == 5) = true <;>
      · simp only [hst, Bool.false_eq_true, ↓reduceIte, Disp.mod]
        spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp, MonadState.get => get_run _]
        rw [setWidth5_beq4]
        simp [AddrMode.reg64, Operand.read, Disp.value, Disp.bytes, BitVec.signExtend]
    | d32 v =>
      by_cases hst : (b == 4 || b == 5) = true <;>
      · simp only [hst, Bool.false_eq_true, ↓reduceIte, Disp.mod]
        spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp, MonadState.get => get_run _]
        rw [setWidth5_beq4]
        simp [AddrMode.reg64, Operand.read, Disp.value, Disp.bytes, BitVec.add_assoc, BitVec.signExtend]

/-- `effectiveAddress_base_run` without a displacement (`mod = 00`; the base is not RBP/R13). -/
theorem effectiveAddress_base_none_run [Bindings] (s : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (h4 : regLow b ≠ 4) (h5 : regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hmode : In64BitMode s) :
    (Effective_Address 64 ctx 0 (regLow b) 1 ip).run s =
      (.ok ((AddrMode.reg64 b s + 0 : BitVec 64), effSegment ctx (if (b == 5) = true then s.SS else s.DS),
        ip + BitVec.ofNat 64 0, false, false), s) := by
  have h4' : (regLow b == 4) = false := by simpa using h4
  have h5' : (regLow b == 5) = false := by simpa using h5
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind, h4', h5',
    HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, hb3, hb4, concatBits_reg4,
    concatBits_hi2, concatBits_reg5, getEffectiveSegment_run_eff ctx _ hm64]
  have hb5 : b ≠ 5 := by
    have : ∀ b : BitVec 4, (regLow b == 5) = false → b ≠ 5 := by decide
    exact this b h5'
  simp only [hb5, ↓reduceIte, beq_iff_eq]
  spec_run [Read_GPR => readGPR64_run _ _ hmode, MonadState.get => get_run _]
  rw [setWidth5_beq4_of_regLow b h4']
  simp [ofValue_eq_mk, AddrMode.reg64, Operand.read]

/-- `effectiveAddress_base_run` with an 8-bit displacement (`mod = 01`). -/
theorem effectiveAddress_base_d8_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (v : BitVec 8) (h4 : regLow b ≠ 4)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hfetch : (Mem_Fetch ip 8).run s = (.ok v, t))
    (hmode : In64BitMode t) :
    (Effective_Address 64 ctx 1 (regLow b) 1 ip).run s =
      (.ok (AddrMode.reg64 b t + v.signExtend 64,
        effSegment ctx (if (b == 5) = true then t.SS else t.DS), ip + BitVec.ofNat 64 1, false, false),
        t) := by
  have h4' : (regLow b == 4) = false := by simpa using h4
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind, h4', HAnd.hAnd,
    AndOp.and, strictAnd, show ((1 : BitVec 2) == 0) = false from rfl, Bool.and_false,
    Bool.false_eq_true, hb3, hb4, concatBits_reg4, concatBits_hi2, concatBits_reg5,
    getEffectiveSegment_run_eff ctx _ hm64]
  by_cases hb5 : b = 5 <;>
  · simp only [hb5, ↓reduceIte, beq_self_eq_true, beq_iff_eq]
    spec_run [Mem_Fetch => hfetch, Read_GPR => readGPR64_run _ _ hmode,
      MonadState.get => get_run _]
    try rw [setWidth5_beq4_of_regLow b h4']
    simp [ofValue_eq_mk, AddrMode.reg64, Operand.read, BitVec.signExtend]

/-- `effectiveAddress_base_run` with a 32-bit displacement (`mod = 10`). -/
theorem effectiveAddress_base_d32_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (v : BitVec 32) (h4 : regLow b ≠ 4)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hfetch : (Mem_Fetch ip 32).run s = (.ok v, t))
    (hmode : In64BitMode t) :
    (Effective_Address 64 ctx 2 (regLow b) 1 ip).run s =
      (.ok (AddrMode.reg64 b t + v.signExtend 64,
        effSegment ctx (if (b == 5) = true then t.SS else t.DS), ip + BitVec.ofNat 64 4, false, false),
        t) := by
  have h4' : (regLow b == 4) = false := by simpa using h4
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind, h4', HAnd.hAnd,
    AndOp.and, strictAnd, show ((2 : BitVec 2) == 0) = false from rfl, Bool.and_false,
    Bool.false_eq_true, hb3, hb4, concatBits_reg4, concatBits_hi2, concatBits_reg5,
    getEffectiveSegment_run_eff ctx _ hm64]
  by_cases hb5 : b = 5 <;>
  · simp only [hb5, ↓reduceIte, beq_self_eq_true, beq_iff_eq]
    spec_run [Mem_Fetch => hfetch, Read_GPR => readGPR64_run _ _ hmode,
      MonadState.get => get_run _]
    try rw [setWidth5_beq4_of_regLow b h4']
    simp [ofValue_eq_mk, AddrMode.reg64, Operand.read, BitVec.signExtend]

/-- `Effective_Address` for `[b + disp]` without a SIB byte, given the displacement fetch. Split
by displacement (`_none`, `_d8`, `_d32`) to keep each proof small for the kernel. -/
theorem effectiveAddress_base_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (d : Disp) (h4 : regLow b ≠ 4) (h5 : d = .none → regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hfetch : d.Fetched ip s t) (hmode : In64BitMode t) :
    (Effective_Address 64 ctx d.mod (regLow b) 1 ip).run s =
      (.ok (AddrMode.reg64 b t + d.value, effSegment ctx (if (b == 5) = true then t.SS else t.DS),
        ip + BitVec.ofNat 64 d.bytes.length, false, false), t) := by
  cases d with
  | none =>
    subst hfetch
    exact effectiveAddress_base_none_run t ctx ip b h4 (h5 rfl) hb3 hb4 hm64 hmode
  | d8 v => exact effectiveAddress_base_d8_run s t ctx ip b v h4 hb3 hb4 hm64 hfetch hmode
  | d32 v => exact effectiveAddress_base_d32_run s t ctx ip b v h4 hb3 hb4 hm64 hfetch hmode

/-- `Effective_Address` with a SIB byte, given its fetches. -/
theorem effectiveAddress_sib_run [Bindings] (s t u : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (i : Option (BitVec 4)) (sc : BitVec 2) (d : Disp)
    (hi4 : i ≠ some 4) (h5 : d = .none → regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0) (hx3 : ctx.rex_x3 = idxHigh i)
    (hx4 : ctx.rex_x4 = 0) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte b i sc).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : d.Fetched (ip + 1) t u) :
    (Effective_Address 64 ctx d.mod 4 1 ip).run s =
      (.ok ((AddrMode.sib b i sc d).addr t 0,
        effSegment ctx (if (b == 4 || b == 5) = true then t.SS else t.DS),
        ip + BitVec.ofNat 64 (1 + d.bytes.length), false, b == 4), u) := by
  have hr := readSIB_run s t u ctx ip b i sc d hi4 h5 hb3 hb4 hx3 hx4 hm64 hsib hmode hdisp
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_eq_ite, ↓reduceIte, pure_bind]
  rw [Disp.mod_bne_three]
  simp only [↓reduceIte, pure_bind]
  spec_run [Read_SIB => hr]
  rw [getEffectiveSegment_run_eff ctx _ hm64, effSegment_idem]
  cases i with
  | none =>
    have k : ∀ x y z : BitVec 64, x + y + (0 : BitVec 64) * z = x + y := by
      intros; simp
    show (Except.ok (_ + _ + (0 : BitVec 64) * _, _, _, _), u) = _
    rw [k]
    rfl
  | some j =>
    show (Except.ok (_ + _ + AddrMode.reg64 j t * BitVec.ofInt 64 ((2 ^ sc.toNat : Nat) : Int), _, _, _), u) = _
    have k : ∀ a c x : BitVec 64, ∀ n : Nat,
        a + c + x * BitVec.ofInt 64 ((2 ^ n : Nat) : Int) = a + x <<< n + c := by
      intros; rw [mul_pow_shift]; ac_rfl
    rw [k]
    rfl

/-- `Effective_Address` for `[rip + disp32]`, given the displacement fetch. -/
theorem effectiveAddress_rip_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (v : BitVec 32)
    (hm64 : ctx.is_mode64 = true) (hfetch : (Mem_Fetch ip 32).run s = (.ok v, t)) :
    (Effective_Address 64 ctx 0 5 1 ip).run s =
      (.ok ((v.signExtend 64 : BitVec 64), effSegment ctx t.DS, (ip + 4 : BitVec 64), true, false), t) := by
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind,
    getEffectiveSegment_run_eff ctx _ hm64, hm64]
  spec_run [Mem_Fetch => hfetch, MonadState.get => get_run _]
  simp [ofValue_eq_mk, BitVec.signExtend] <;> rfl

/-- `Read_SIB` with `mod = 00` and SIB base field `101` (no base: `[index * 2^scale + disp32]`),
given its fetches. -/
theorem readSIB_abs_run [Bindings] (s t u : RamState) (ctx : Instruction_Context) (ip : BitVec 64)
    (i : Option (BitVec 4)) (sc : BitVec 2) (v : BitVec 32) (hi4 : i ≠ some 4)
    (hb3 : ctx.rex_b3 = 0) (hb4 : ctx.rex_b4 = 0) (hx3 : ctx.rex_x3 = idxHigh i)
    (hx4 : ctx.rex_x4 = 0) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte 5 i sc).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : (Mem_Fetch (ip + 1 : BitVec 64) 32).run t = (.ok v, u)) :
    (Read_SIB ctx 0 1 ip).run s =
      (.ok (effSegment ctx u.DS, v.signExtend 64,
        (match i with | some j => AddrMode.reg64 j t | none => 0),
        ((2 ^ sc.toNat : Nat) : Int), (ip + 5 : BitVec 64), false), u) := by
  unfold Read_SIB
  refine (specM_bind_run _ _ hsib).trans ?_
  simp (config := { decide := true }) only [sliceInclusive_eq,
    X86.Runtime.CheckedSlice.read, slice_eq_pure, pure_bind, Int.reduceToNat, Int.reduceSub,
    Int.reduceAdd, sibByte_toBitVec, append_hi, append_mid, append_lo, exp2_scale, hb3, hb4, hx3,
    hx4, concatBits_hi2, HOr.hOr, OrOp.or, strictOr,
    getEffectiveSegment_run_eff ctx _ hm64]
  cases i with
  | none =>
    simp (config := { decide := true }) only [idxHigh, idxLow, concatBits_none5, pure_bind,
      ↓reduceIte]
    spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp, MonadState.get => get_run _]
  | some j =>
    have hj : j ≠ 4 := fun h => hi4 (h ▸ rfl)
    simp (config := { decide := true }) only [idxHigh, idxLow, concatBits_reg5, pure_bind,
      ↓reduceIte, setWidth5_ne4 j hj]
    spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hdisp, MonadState.get => get_run _]

/-- `Effective_Address` for `[index * 2^scale + disp32]` (SIB, no base), given its fetches. -/
theorem effectiveAddress_abs_run [Bindings] (s t u : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (i : Option (BitVec 4)) (sc : BitVec 2) (v : BitVec 32) (hi4 : i ≠ some 4)
    (hb3 : ctx.rex_b3 = 0) (hb4 : ctx.rex_b4 = 0) (hx3 : ctx.rex_x3 = idxHigh i)
    (hx4 : ctx.rex_x4 = 0) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte 5 i sc).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : (Mem_Fetch (ip + 1 : BitVec 64) 32).run t = (.ok v, u)) :
    (Effective_Address 64 ctx 0 4 1 ip).run s =
      (.ok ((AddrMode.abs i sc v).addr t 0, effSegment ctx u.DS, (ip + 5 : BitVec 64), false, false),
        u) := by
  have hr := readSIB_abs_run s t u ctx ip i sc v hi4 hb3 hb4 hx3 hx4 hm64 hsib hmode hdisp
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_eq_ite, ↓reduceIte, pure_bind]
  spec_run [Read_SIB => hr]
  rw [getEffectiveSegment_run_eff ctx _ hm64, effSegment_idem]
  cases i with
  | none =>
    show (Except.ok (_ + (0 : BitVec 64) * _, _, _, _), u) = _
    simp [AddrMode.addr]
  | some j =>
    show (Except.ok (_ + AddrMode.reg64 j t * BitVec.ofInt 64 ((2 ^ sc.toNat : Nat) : Int), _, _, _),
      u) = _
    rw [mul_pow_shift]
    simp [AddrMode.addr, BitVec.add_comm]

/-! ### From the instruction bytes -/

/-- Fetching a displacement stored at offset `i` of the instruction at RIP. -/
theorem disp_fetched [Bindings] (s : RamState) (k : Nat) (h : FetchReady s) {bytes : List UInt8}
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (d : Disp) (i : Nat)
    (hd : ∀ j < d.bytes.length, bytes[i + j]? = d.bytes[j]?) (hlen : i + d.bytes.length ≤ bytes.length)
    (h15 : i + d.bytes.length ≤ 15) :
    d.Fetched (BitVec.add s.RIP (BitVec.ofNat 64 i)) (afterFetches s k)
      (afterFetches s (k + d.bytes.length)) := by
  cases d with
  | none => rfl
  | d8 v =>
    refine memFetch_run_of_bytesAt_imm s k h hcode hlow 8 (by decide) v i (fun j hj => ?_) hlen h15
    rw [hd j hj]; exact immBytes_getElem? v hj
  | d32 v =>
    refine memFetch_run_of_bytesAt_imm s k h hcode hlow 32 (by decide) v i (fun j hj => ?_) hlen h15
    rw [hd j hj]; exact immBytes_getElem? v hj

/-- The segment of a 64-bit data access from SS or DS after the decode context `ctx`. -/
theorem effSegment_stack (s : RamState) (hds : s.DS = {userStackSegment with is_stack := some false})
    (hss : s.SS = userStackSegment) (ctx : Instruction_Context) (b : Bool) :
    effSegment ctx (if b = true then s.SS else s.DS) = ctxSegment ctx b := by
  unfold effSegment ctxSegment
  rw [nullDataSegment_stack s hds hss]

/--
The address computation, run where the decoder runs it, with any segment prefix. If the
instruction at RIP (`bytes`, below 4 GiB) has `am.tail` at offset `i`, and `k` bytes were fetched,
`Effective_Address` with `am.mod`, `am.rm` and address size 64 fetches exactly `am.tail` (one
fetch per byte) and returns `am.offset s`, the segment `ctxSegment ctx am.isStack` (the FS or GS
segment after a segment prefix, else the flat segment `flatData am.isStack`), the address after the
tail, whether the operand is RIP-relative and whether its base is RSP.
-/
theorem effectiveAddress_run_seg [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    (hds : s.DS = {userStackSegment with is_stack := some false}) (hss : s.SS = userStackSegment)
    (am : AddrMode) (hv : am.Valid) (ctx : Instruction_Context) (hctx : SegAddrContext ctx am)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (i : Nat) (htail : ∀ j < am.tail.length, bytes[i + j]? = am.tail[j]?)
    (hlen : i + am.tail.length ≤ bytes.length) (h15 : i + am.tail.length ≤ 15) :
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 i))).run
        (afterFetches s k) =
      (.ok (am.offset s, ctxSegment ctx am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (i + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches s (k + am.tail.length)) := by
  have hmode (k' : Nat) : In64BitMode (afterFetches s k') :=
    in64BitMode_of_userCodeSegment (s := afterFetches s k') h.cs h.efer.lma
  have hseg := effSegment_stack (afterFetches s (k + am.tail.length)) hds hss ctx
  cases am with
  | base b d =>
    obtain ⟨h4, h5⟩ := hv
    have hf := disp_fetched s k h hcode hlow d i htail hlen h15
    refine (effectiveAddress_base_run _ _ ctx _ b d h4 h5 hctx.b3 hctx.b4 hctx.mode64 hf
      (hmode _)).trans ?_
    simp only [AddrMode.tail] at hseg ⊢
    rw [hseg, ← BitVec.add_eq (BitVec.add _ _), add_ofNat_add]
    rfl
  | sib b ix sc d =>
    obtain ⟨hi4, h5⟩ := hv
    have hil : i < bytes.length := by simp [AddrMode.tail] at hlen; omega
    have hsib := memFetch_run_of_bytesAt s k h hcode hlow i hil (by simp [AddrMode.tail] at h15; omega)
    have hsb : bytes[i] = AddrMode.sibByte b ix sc := by
      have := htail 0 (by simp [AddrMode.tail])
      simp only [Nat.add_zero, AddrMode.tail, List.getElem?_cons_zero] at this
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
    rw [hsb] at hsib
    have hf := disp_fetched s (k + 1) h hcode hlow d (i + 1)
      (fun j hj => by
        have := htail (j + 1) (by simp [AddrMode.tail]; omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this)
      (by simp [AddrMode.tail] at hlen; omega) (by simp [AddrMode.tail] at h15; omega)
    have hip : BitVec.add s.RIP (BitVec.ofNat 64 (i + 1)) =
        BitVec.add s.RIP (BitVec.ofNat 64 i) + 1 := (add_ofNat_add s.RIP i 1).symm
    rw [hip] at hf
    refine (effectiveAddress_sib_run _ _ _ ctx _ b ix sc d hi4 h5 hctx.b3 hctx.b4 hctx.x3 hctx.x4
      hctx.mode64 hsib (hmode _) hf).trans ?_
    have hseg' := effSegment_stack (afterFetches s (k + 1)) hds hss ctx
    simp only [AddrMode.tail, List.length_cons] at hseg ⊢
    rw [hseg', ← BitVec.add_eq (BitVec.add _ _), add_ofNat_add, show k + 1 + d.bytes.length = k + (d.bytes.length + 1) by omega,
      show 1 + d.bytes.length = d.bytes.length + 1 by omega]
    cases ix <;> rfl
  | rip v =>
    have hf := memFetch_run_of_bytesAt_imm s k h hcode hlow 32 (by decide) v i
      (fun j hj => by rw [htail j (by simpa [AddrMode.tail] using hj)]; exact immBytes_getElem? v hj)
      (by simpa [AddrMode.tail] using hlen) (by simpa [AddrMode.tail] using h15)
    refine (effectiveAddress_rip_run _ _ ctx _ v hctx.mode64 hf).trans ?_
    have hseg' := effSegment_stack (afterFetches s (k + 32 / 8)) hds hss ctx false
    simp only [Bool.false_eq_true, ↓reduceIte] at hseg'
    have hip : BitVec.add s.RIP (BitVec.ofNat 64 i) + 4 =
        BitVec.add s.RIP (BitVec.ofNat 64 (i + 32 / 8)) := add_ofNat_add s.RIP i 4
    rw [hip]
    simp only [AddrMode.tail, immBytes_length, hseg']
    rfl
  | abs ix sc v =>
    have hil : i < bytes.length := by simp [AddrMode.tail] at hlen; omega
    have hsib := memFetch_run_of_bytesAt s k h hcode hlow i hil (by simp [AddrMode.tail] at h15; omega)
    have hsb : bytes[i] = AddrMode.sibByte 5 ix sc := by
      have := htail 0 (by simp [AddrMode.tail])
      simp only [Nat.add_zero, AddrMode.tail, List.getElem?_cons_zero] at this
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
    rw [hsb] at hsib
    have hf := memFetch_run_of_bytesAt_imm s (k + 1) h hcode hlow 32 (by decide) v (i + 1)
      (fun j hj => by
        have := htail (j + 1) (by simp [AddrMode.tail]; omega)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        rw [this]
        exact immBytes_getElem? v hj)
      (by simp [AddrMode.tail] at hlen; omega) (by simp [AddrMode.tail] at h15; omega)
    have hip : BitVec.add s.RIP (BitVec.ofNat 64 (i + 1)) =
        BitVec.add s.RIP (BitVec.ofNat 64 i) + 1 := (add_ofNat_add s.RIP i 1).symm
    rw [hip] at hf
    refine (effectiveAddress_abs_run _ _ _ ctx _ ix sc v hv hctx.b3 hctx.b4 hctx.x3 hctx.x4
      hctx.mode64 hsib (hmode _) hf).trans ?_
    have hseg' := effSegment_stack (afterFetches s (k + 1 + 32 / 8)) hds hss ctx false
    simp only [Bool.false_eq_true, ↓reduceIte] at hseg'
    have hip5 : BitVec.add s.RIP (BitVec.ofNat 64 i) + 5 =
        BitVec.add s.RIP (BitVec.ofNat 64 (i + 5)) := add_ofNat_add s.RIP i 5
    rw [hip5, hseg']
    simp only [AddrMode.tail, List.length_cons, immBytes_length]
    rw [show k + 1 + 32 / 8 = k + (32 / 8 + 1) by omega]
    cases ix <;> rfl

/--
The address computation, run where the decoder runs it, without a segment prefix
(`effectiveAddress_run_seg` for `AddrContext`): the segment is the flat segment
`flatData am.isStack`.
-/
theorem effectiveAddress_run [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    (hds : s.DS = {userStackSegment with is_stack := some false}) (hss : s.SS = userStackSegment)
    (am : AddrMode) (hv : am.Valid) (ctx : Instruction_Context) (hctx : AddrContext ctx am)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (i : Nat) (htail : ∀ j < am.tail.length, bytes[i + j]? = am.tail[j]?)
    (hlen : i + am.tail.length ≤ bytes.length) (h15 : i + am.tail.length ≤ 15) :
    (Effective_Address 64 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 i))).run
        (afterFetches s k) =
      (.ok (am.offset s, flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (i + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches s (k + am.tail.length)) := by
  rw [effectiveAddress_run_seg s k h hds hss am hv ctx hctx.toSeg hcode hlow i htail hlen h15]
  simp [ctxSegment, hctx.seg]

theorem handleRIPRelativeAddress64_run (isRip : Bool) (off next : BitVec 64) :
    Handle_RIP_Relative_Address 64 isRip off next = .ok (if isRip then off + next else off) := by
  simp only [Handle_RIP_Relative_Address, x86_runtime]
  cases isRip <;> simp [assert_of_true, bind, pure, Except.bind, Except.pure]

/-- `Handle_RIP_Relative_Address` at address size 64 turns `am.offset` into `am.addr`, given the
address after the displacement. -/
theorem handleRIPRelativeAddress_addrMode_run (am : AddrMode) (s : RamState) (next : BitVec 64) :
    Handle_RIP_Relative_Address 64 am.isRip (am.offset s) next = .ok (am.addr s next) := by
  rw [handleRIPRelativeAddress64_run]
  cases am with
  | rip d => simp [AddrMode.isRip, AddrMode.offset, AddrMode.addr, BitVec.add_comm]
  | base b d => rfl
  | sib b i sc d => cases i <;> rfl
  | abs i sc d => cases i <;> rfl

/-- `Handle_RIP_Relative_Address` at address size 64 of `am.offset` plus `d` (BT, BTS, BTR, BTC add
their bit-string offset before it) is `am.addr` plus `d`. -/
theorem handleRIPRelativeAddress_addrMode_add_run (am : AddrMode) (s : RamState)
    (next d : BitVec 64) :
    Handle_RIP_Relative_Address 64 am.isRip (am.offset s + d) next = .ok (am.addr s next + d) := by
  have h := handleRIPRelativeAddress_addrMode_run am s next
  rw [handleRIPRelativeAddress64_run] at h ⊢
  cases hr : am.isRip <;> simp only [hr, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h ⊢
  · rw [h]
  · rw [← h, BitVec.add_assoc, BitVec.add_comm d, ← BitVec.add_assoc]

/-- In 64-bit mode without an address-size prefix (`67`), lean-x86's `Address_Size` is 64 and
leaves the state unchanged. -/
theorem addressSize_run (ctx : Instruction_Context) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false) (s : RamState) :
    (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run s = (.ok 64, s) := by
  rw [addressSize_mode64_run ctx hm64, hasz]
  rfl

/-! ### Address size 32 (`67`)

With an address-size prefix lean-x86's `Effective_Address` runs at address size 32: the SIB,
RIP-relative and no-base forms compute the same 64-bit sum as at address size 64, the base-only
form reads the base's low 32 bits (sign-extended); `Handle_RIP_Relative_Address` then keeps the
low 32 bits of the result, zero-extended (`AddrMode.addr32`). -/

/-- `effectiveAddress32_base_run` without a displacement. -/
theorem effectiveAddress32_base_none_run [Bindings] (s : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (h4 : regLow b ≠ 4) (h5 : regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hmode : In64BitMode s) :
    (Effective_Address 32 ctx 0 (regLow b) 1 ip).run s =
      (.ok ((AddrMode.base b .none).offset32 s,
        effSegment ctx (if (b == 5) = true then s.SS else s.DS), ip + BitVec.ofNat 64 0, false, false),
        s) := by
  have h4' : (regLow b == 4) = false := by simpa using h4
  have h5' : (regLow b == 5) = false := by simpa using h5
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind, h4', h5',
    HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, hb3, hb4, concatBits_reg4,
    concatBits_hi2, concatBits_reg5, getEffectiveSegment_run_eff ctx _ hm64]
  have hb5 : b ≠ 5 := by
    have : ∀ b : BitVec 4, (regLow b == 5) = false → b ≠ 5 := by decide
    exact this b h5'
  simp only [hb5, ↓reduceIte, beq_iff_eq]
  spec_run [Read_GPR => readGPR32_run _ _ hmode, MonadState.get => get_run _]
  rw [setWidth5_beq4_of_regLow b h4']
  simp [ofValue_eq_mk, AddrMode.offset32, AddrMode.reg64, Operand.read, Disp.value,
    BitVec.signExtend]

/-- `effectiveAddress32_base_run` with an 8-bit displacement. -/
theorem effectiveAddress32_base_d8_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (v : BitVec 8) (h4 : regLow b ≠ 4)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hfetch : (Mem_Fetch ip 8).run s = (.ok v, t))
    (hmode : In64BitMode t) :
    (Effective_Address 32 ctx 1 (regLow b) 1 ip).run s =
      (.ok ((AddrMode.base b (.d8 v)).offset32 t,
        effSegment ctx (if (b == 5) = true then t.SS else t.DS), ip + BitVec.ofNat 64 1, false, false),
        t) := by
  have h4' : (regLow b == 4) = false := by simpa using h4
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind, h4', HAnd.hAnd,
    AndOp.and, strictAnd, show ((1 : BitVec 2) == 0) = false from rfl, Bool.and_false,
    Bool.false_eq_true, hb3, hb4, concatBits_reg4, concatBits_hi2, concatBits_reg5,
    getEffectiveSegment_run_eff ctx _ hm64]
  by_cases hb5 : b = 5 <;>
  · simp only [hb5, ↓reduceIte, beq_self_eq_true, beq_iff_eq]
    spec_run [Mem_Fetch => hfetch, Read_GPR => readGPR32_run _ _ hmode,
      MonadState.get => get_run _]
    try rw [setWidth5_beq4_of_regLow b h4']
    simp [ofValue_eq_mk, AddrMode.offset32, AddrMode.reg64, Operand.read, Disp.value,
      BitVec.signExtend]

/-- `effectiveAddress32_base_run` with a 32-bit displacement. -/
theorem effectiveAddress32_base_d32_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (v : BitVec 32) (h4 : regLow b ≠ 4)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hfetch : (Mem_Fetch ip 32).run s = (.ok v, t))
    (hmode : In64BitMode t) :
    (Effective_Address 32 ctx 2 (regLow b) 1 ip).run s =
      (.ok ((AddrMode.base b (.d32 v)).offset32 t,
        effSegment ctx (if (b == 5) = true then t.SS else t.DS), ip + BitVec.ofNat 64 4, false, false),
        t) := by
  have h4' : (regLow b == 4) = false := by simpa using h4
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind, h4', HAnd.hAnd,
    AndOp.and, strictAnd, show ((2 : BitVec 2) == 0) = false from rfl, Bool.and_false,
    Bool.false_eq_true, hb3, hb4, concatBits_reg4, concatBits_hi2, concatBits_reg5,
    getEffectiveSegment_run_eff ctx _ hm64]
  by_cases hb5 : b = 5 <;>
  · simp only [hb5, ↓reduceIte, beq_self_eq_true, beq_iff_eq]
    spec_run [Mem_Fetch => hfetch, Read_GPR => readGPR32_run _ _ hmode,
      MonadState.get => get_run _]
    try rw [setWidth5_beq4_of_regLow b h4']
    simp [ofValue_eq_mk, AddrMode.offset32, AddrMode.reg64, Operand.read, Disp.value,
      BitVec.signExtend]

/-- `Effective_Address` at address size 32 for `[b + disp]` without a SIB byte, given the
displacement fetch: the base's low 32 bits, sign-extended, plus the displacement. -/
theorem effectiveAddress32_base_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (d : Disp) (h4 : regLow b ≠ 4) (h5 : d = .none → regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0)
    (hm64 : ctx.is_mode64 = true) (hfetch : d.Fetched ip s t) (hmode : In64BitMode t) :
    (Effective_Address 32 ctx d.mod (regLow b) 1 ip).run s =
      (.ok ((AddrMode.base b d).offset32 t,
        effSegment ctx (if (b == 5) = true then t.SS else t.DS),
        ip + BitVec.ofNat 64 d.bytes.length, false, false), t) := by
  cases d with
  | none =>
    subst hfetch
    exact effectiveAddress32_base_none_run t ctx ip b h4 (h5 rfl) hb3 hb4 hm64 hmode
  | d8 v => exact effectiveAddress32_base_d8_run s t ctx ip b v h4 hb3 hb4 hm64 hfetch hmode
  | d32 v => exact effectiveAddress32_base_d32_run s t ctx ip b v h4 hb3 hb4 hm64 hfetch hmode

/-- `Effective_Address` at address size 32 with a SIB byte, given its fetches: as at address size
64 (`effectiveAddress_sib_run`). -/
theorem effectiveAddress32_sib_run [Bindings] (s t u : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (b : BitVec 4) (i : Option (BitVec 4)) (sc : BitVec 2) (d : Disp)
    (hi4 : i ≠ some 4) (h5 : d = .none → regLow b ≠ 5)
    (hb3 : ctx.rex_b3 = regHigh b) (hb4 : ctx.rex_b4 = 0) (hx3 : ctx.rex_x3 = idxHigh i)
    (hx4 : ctx.rex_x4 = 0) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte b i sc).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : d.Fetched (ip + 1) t u) :
    (Effective_Address 32 ctx d.mod 4 1 ip).run s =
      (.ok ((AddrMode.sib b i sc d).addr t 0,
        effSegment ctx (if (b == 4 || b == 5) = true then t.SS else t.DS),
        ip + BitVec.ofNat 64 (1 + d.bytes.length), false, b == 4), u) := by
  have hr := readSIB_run s t u ctx ip b i sc d hi4 h5 hb3 hb4 hx3 hx4 hm64 hsib hmode hdisp
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_eq_ite, ↓reduceIte, pure_bind]
  rw [Disp.mod_bne_three]
  simp only [↓reduceIte, pure_bind]
  spec_run [Read_SIB => hr]
  rw [getEffectiveSegment_run_eff ctx _ hm64, effSegment_idem]
  cases i with
  | none =>
    have k : ∀ x y z : BitVec 64, x + y + (0 : BitVec 64) * z = x + y := by
      intros; simp
    show (Except.ok (_ + _ + (0 : BitVec 64) * _, _, _, _), u) = _
    rw [k]
    rfl
  | some j =>
    show (Except.ok (_ + _ + AddrMode.reg64 j t * BitVec.ofInt 64 ((2 ^ sc.toNat : Nat) : Int), _, _, _), u) = _
    have k : ∀ a c x : BitVec 64, ∀ n : Nat,
        a + c + x * BitVec.ofInt 64 ((2 ^ n : Nat) : Int) = a + x <<< n + c := by
      intros; rw [mul_pow_shift]; ac_rfl
    rw [k]
    rfl

/-- `Effective_Address` at address size 32 for `[rip + disp32]` (EIP-relative), given the
displacement fetch: as at address size 64 (`effectiveAddress_rip_run`). -/
theorem effectiveAddress32_rip_run [Bindings] (s t : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (v : BitVec 32)
    (hm64 : ctx.is_mode64 = true) (hfetch : (Mem_Fetch ip 32).run s = (.ok v, t)) :
    (Effective_Address 32 ctx 0 5 1 ip).run s =
      (.ok ((v.signExtend 64 : BitVec 64), effSegment ctx t.DS, (ip + 4 : BitVec 64), true, false), t) := by
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind,
    getEffectiveSegment_run_eff ctx _ hm64, hm64]
  spec_run [Mem_Fetch => hfetch, MonadState.get => get_run _]
  simp [ofValue_eq_mk, BitVec.signExtend] <;> rfl

/-- `Effective_Address` at address size 32 for `[index * 2^scale + disp32]` (SIB, no base), given
its fetches: as at address size 64 (`effectiveAddress_abs_run`). -/
theorem effectiveAddress32_abs_run [Bindings] (s t u : RamState) (ctx : Instruction_Context)
    (ip : BitVec 64) (i : Option (BitVec 4)) (sc : BitVec 2) (v : BitVec 32) (hi4 : i ≠ some 4)
    (hb3 : ctx.rex_b3 = 0) (hb4 : ctx.rex_b4 = 0) (hx3 : ctx.rex_x3 = idxHigh i)
    (hx4 : ctx.rex_x4 = 0) (hm64 : ctx.is_mode64 = true)
    (hsib : (Mem_Fetch ip 8).run s = (.ok (AddrMode.sibByte 5 i sc).toBitVec, t))
    (hmode : In64BitMode t) (hdisp : (Mem_Fetch (ip + 1 : BitVec 64) 32).run t = (.ok v, u)) :
    (Effective_Address 32 ctx 0 4 1 ip).run s =
      (.ok ((AddrMode.abs i sc v).addr t 0, effSegment ctx u.DS, (ip + 5 : BitVec 64), false, false),
        u) := by
  have hr := readSIB_abs_run s t u ctx ip i sc v hi4 hb3 hb4 hx3 hx4 hm64 hsib hmode hdisp
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_eq_ite, ↓reduceIte, pure_bind]
  spec_run [Read_SIB => hr]
  rw [getEffectiveSegment_run_eff ctx _ hm64, effSegment_idem]
  cases i with
  | none =>
    show (Except.ok (_ + (0 : BitVec 64) * _, _, _, _), u) = _
    simp [AddrMode.addr]
  | some j =>
    show (Except.ok (_ + AddrMode.reg64 j t * BitVec.ofInt 64 ((2 ^ sc.toNat : Nat) : Int), _, _, _),
      u) = _
    rw [mul_pow_shift]
    simp [AddrMode.addr, BitVec.add_comm]

/--
The address computation at address size 32 (`67`), run where the decoder runs it, with any segment
prefix: as `effectiveAddress_run_seg`, returning `am.offset32 s` (which
`handleRIPRelativeAddress_addrMode32_run` turns into `am.addr32`).
-/
theorem effectiveAddress32_run_seg [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    (hds : s.DS = {userStackSegment with is_stack := some false}) (hss : s.SS = userStackSegment)
    (am : AddrMode) (hv : am.Valid) (ctx : Instruction_Context) (hctx : SegAddrContext ctx am)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (i : Nat) (htail : ∀ j < am.tail.length, bytes[i + j]? = am.tail[j]?)
    (hlen : i + am.tail.length ≤ bytes.length) (h15 : i + am.tail.length ≤ 15) :
    (Effective_Address 32 ctx am.mod am.rm 1 (BitVec.add s.RIP (BitVec.ofNat 64 i))).run
        (afterFetches s k) =
      (.ok (am.offset32 s, ctxSegment ctx am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (i + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches s (k + am.tail.length)) := by
  have hmode (k' : Nat) : In64BitMode (afterFetches s k') :=
    in64BitMode_of_userCodeSegment (s := afterFetches s k') h.cs h.efer.lma
  have hseg := effSegment_stack (afterFetches s (k + am.tail.length)) hds hss ctx
  cases am with
  | base b d =>
    obtain ⟨h4, h5⟩ := hv
    have hf := disp_fetched s k h hcode hlow d i htail hlen h15
    refine (effectiveAddress32_base_run _ _ ctx _ b d h4 h5 hctx.b3 hctx.b4 hctx.mode64 hf
      (hmode _)).trans ?_
    simp only [AddrMode.tail] at hseg ⊢
    rw [hseg, ← BitVec.add_eq (BitVec.add _ _), add_ofNat_add]
    rfl
  | sib b ix sc d =>
    obtain ⟨hi4, h5⟩ := hv
    have hil : i < bytes.length := by simp [AddrMode.tail] at hlen; omega
    have hsib := memFetch_run_of_bytesAt s k h hcode hlow i hil (by simp [AddrMode.tail] at h15; omega)
    have hsb : bytes[i] = AddrMode.sibByte b ix sc := by
      have := htail 0 (by simp [AddrMode.tail])
      simp only [Nat.add_zero, AddrMode.tail, List.getElem?_cons_zero] at this
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
    rw [hsb] at hsib
    have hf := disp_fetched s (k + 1) h hcode hlow d (i + 1)
      (fun j hj => by
        have := htail (j + 1) (by simp [AddrMode.tail]; omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this)
      (by simp [AddrMode.tail] at hlen; omega) (by simp [AddrMode.tail] at h15; omega)
    have hip : BitVec.add s.RIP (BitVec.ofNat 64 (i + 1)) =
        BitVec.add s.RIP (BitVec.ofNat 64 i) + 1 := (add_ofNat_add s.RIP i 1).symm
    rw [hip] at hf
    refine (effectiveAddress32_sib_run _ _ _ ctx _ b ix sc d hi4 h5 hctx.b3 hctx.b4 hctx.x3 hctx.x4
      hctx.mode64 hsib (hmode _) hf).trans ?_
    have hseg' := effSegment_stack (afterFetches s (k + 1)) hds hss ctx
    simp only [AddrMode.tail, List.length_cons] at hseg ⊢
    rw [hseg', ← BitVec.add_eq (BitVec.add _ _), add_ofNat_add, show k + 1 + d.bytes.length = k + (d.bytes.length + 1) by omega,
      show 1 + d.bytes.length = d.bytes.length + 1 by omega]
    cases ix <;> rfl
  | rip v =>
    have hf := memFetch_run_of_bytesAt_imm s k h hcode hlow 32 (by decide) v i
      (fun j hj => by rw [htail j (by simpa [AddrMode.tail] using hj)]; exact immBytes_getElem? v hj)
      (by simpa [AddrMode.tail] using hlen) (by simpa [AddrMode.tail] using h15)
    refine (effectiveAddress32_rip_run _ _ ctx _ v hctx.mode64 hf).trans ?_
    have hseg' := effSegment_stack (afterFetches s (k + 32 / 8)) hds hss ctx false
    simp only [Bool.false_eq_true, ↓reduceIte] at hseg'
    have hip : BitVec.add s.RIP (BitVec.ofNat 64 i) + 4 =
        BitVec.add s.RIP (BitVec.ofNat 64 (i + 32 / 8)) := add_ofNat_add s.RIP i 4
    rw [hip]
    simp only [AddrMode.tail, immBytes_length, hseg']
    rfl
  | abs ix sc v =>
    have hil : i < bytes.length := by simp [AddrMode.tail] at hlen; omega
    have hsib := memFetch_run_of_bytesAt s k h hcode hlow i hil (by simp [AddrMode.tail] at h15; omega)
    have hsb : bytes[i] = AddrMode.sibByte 5 ix sc := by
      have := htail 0 (by simp [AddrMode.tail])
      simp only [Nat.add_zero, AddrMode.tail, List.getElem?_cons_zero] at this
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)
    rw [hsb] at hsib
    have hf := memFetch_run_of_bytesAt_imm s (k + 1) h hcode hlow 32 (by decide) v (i + 1)
      (fun j hj => by
        have := htail (j + 1) (by simp [AddrMode.tail]; omega)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        rw [this]
        exact immBytes_getElem? v hj)
      (by simp [AddrMode.tail] at hlen; omega) (by simp [AddrMode.tail] at h15; omega)
    have hip : BitVec.add s.RIP (BitVec.ofNat 64 (i + 1)) =
        BitVec.add s.RIP (BitVec.ofNat 64 i) + 1 := (add_ofNat_add s.RIP i 1).symm
    rw [hip] at hf
    refine (effectiveAddress32_abs_run _ _ _ ctx _ ix sc v hv hctx.b3 hctx.b4 hctx.x3 hctx.x4
      hctx.mode64 hsib (hmode _) hf).trans ?_
    have hseg' := effSegment_stack (afterFetches s (k + 1 + 32 / 8)) hds hss ctx false
    simp only [Bool.false_eq_true, ↓reduceIte] at hseg'
    have hip5 : BitVec.add s.RIP (BitVec.ofNat 64 i) + 5 =
        BitVec.add s.RIP (BitVec.ofNat 64 (i + 5)) := add_ofNat_add s.RIP i 5
    rw [hip5, hseg']
    simp only [AddrMode.tail, List.length_cons, immBytes_length]
    rw [show k + 1 + 32 / 8 = k + (32 / 8 + 1) by omega]
    cases ix <;> rfl

theorem handleRIPRelativeAddress32_run (isRip : Bool) (off next : BitVec 64) :
    Handle_RIP_Relative_Address 32 isRip off next =
      .ok (((if isRip then off + next else off).setWidth 32).setWidth 64) := by
  simp only [Handle_RIP_Relative_Address, x86_runtime]
  cases isRip <;> simp [assert_of_true, bind, pure, Except.bind, Except.pure,
    BitVec.setWidth_eq_extractLsb']

theorem setWidth32_signExtend_setWidth32 (x : BitVec 64) :
    ((x.setWidth 32).signExtend 64).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

/-- `Handle_RIP_Relative_Address` at address size 32 turns `am.offset32` into `am.addr32`, given the
address after the displacement. -/
theorem handleRIPRelativeAddress_addrMode32_run (am : AddrMode) (s : RamState)
    (next : BitVec 64) :
    Handle_RIP_Relative_Address 32 am.isRip (am.offset32 s) next = .ok (am.addr32 s next) := by
  rw [handleRIPRelativeAddress32_run]
  cases am with
  | rip d => simp [AddrMode.isRip, AddrMode.offset32, AddrMode.offset, AddrMode.addr32,
      AddrMode.addr, BitVec.add_comm]
  | base b d =>
    simp only [AddrMode.isRip, AddrMode.offset32, AddrMode.addr32, AddrMode.addr,
      Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.setWidth_add (i := 32) _ _ (by decide),
      BitVec.setWidth_add (i := 32) _ _ (by decide), setWidth32_signExtend_setWidth32]
  | sib b i sc d => cases i <;> rfl
  | abs i sc d => cases i <;> rfl

/-- `Handle_RIP_Relative_Address` at address size 32 of `am.offset32` plus `d` (BT, BTS, BTR, BTC
add their bit-string offset before it): the low 32 bits of `am.addr` plus `d`, zero-extended. -/
theorem handleRIPRelativeAddress_addrMode32_add_run (am : AddrMode) (s : RamState)
    (next d : BitVec 64) :
    Handle_RIP_Relative_Address 32 am.isRip (am.offset32 s + d) next =
      .ok (((am.addr s next + d).setWidth 32).setWidth 64) := by
  have h := handleRIPRelativeAddress_addrMode32_run am s next
  rw [handleRIPRelativeAddress32_run] at h ⊢
  simp only [Except.ok.injEq, AddrMode.addr32] at h ⊢
  have h' := congrArg (BitVec.setWidth 32) h
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] at h'
  congr 1
  cases hr : am.isRip <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at h' ⊢
  · rw [BitVec.setWidth_add (i := 32) _ _ (by decide), h',
      ← BitVec.setWidth_add (i := 32) _ _ (by decide)]
  · rw [show am.offset32 s + d + next = (am.offset32 s + next) + d by ac_rfl,
      BitVec.setWidth_add (i := 32) _ _ (by decide), h',
      ← BitVec.setWidth_add (i := 32) _ _ (by decide)]

/-! ### Direct memory offsets (`moffs`) -/

/-- The decode-context facts the address of a `moffs` operand (`MOV AL/rAX, moffs`, `MOV moffs,
AL/rAX`: opcodes `A0`–`A3`) reads: address size 64, no segment prefix, 64-bit mode, and the
default segment `ds` (DS). -/
structure MoffsContext (ctx : Instruction_Context) (ds : X86.Helpers.Segment) : Prop where
  addr : ctx.address_size = 64
  seg : ctx.seg_prefix_present = false
  mode64 : ctx.is_mode64 = true
  segment : ctx.segment = ds

/--
lean-x86's `Direct_Memory_Offset` at address size 64, run where the `A0`–`A3` forms run it (`k`
byte fetches done, the 8-byte offset `moffs` stored at offset `i` of the instruction at RIP): it
fetches the offset and returns the flat data segment (DS, base 0), `moffs` as the address, and the
address after it. LAM is not reported (`FetchReady.lam`), so the offset is not canonicalized.
-/
theorem directMemoryOffset_run [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    (hds : s.DS = {userStackSegment with is_stack := some false})
    (ctx : Instruction_Context) (hctx : MoffsContext ctx s.DS)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (moffs : BitVec 64) (i : Nat) (hbytes : ∀ j < 8, bytes[i + j]? = some (immByte moffs j))
    (hlen : i + 8 ≤ bytes.length) (h15 : i + 8 ≤ 15) :
    (Direct_Memory_Offset 64 ctx (BitVec.add s.RIP (BitVec.ofNat 64 i))).run (afterFetches s k) =
      (.ok (flatData false, moffs, BitVec.add s.RIP (BitVec.ofNat 64 (i + 8))),
        afterFetches s (k + 8)) := by
  have hfetch := memFetch_run_of_bytesAt_imm64 s k h hcode hlow moffs i hbytes hlen h15
  have hlam := cpuidLAM_run (afterFetches s (k + 8))
    (reportsCPUFeature_of_sameControls (SameControls.afterFetches s (k + 8)) h.lam)
  have hges : Get_Effective_Segment ctx ctx.segment = .ok (flatData false) := by
    rw [getEffectiveSegment_run ctx ctx.segment hctx.seg hctx.mode64, hctx.segment, hds]
    rfl
  unfold Direct_Memory_Offset
  simp only [hges]
  spec_run [
    Mem_Fetch => hfetch,
    CPUID_LAM => hlam]
  rw [← add_ofNat_add]
  have hv : BitVec.ofNat (Int.toNat 64) moffs.toNat = moffs := by
    rw [BitVec.ofNat_toNat]; exact BitVec.setWidth_eq moffs
  rw [hv]
  rfl

/-- The decode-context facts the address of a `moffs` operand reads when it may have a segment
override: address size 64, 64-bit mode, and the segment of the access, `ctxSegment ctx false`:
without a segment prefix the default segment `ds` (DS), with one (FS or GS) a segment ready for
data accesses (`SegReady`). -/
structure SegMoffsContext (ctx : Instruction_Context) (ds : X86.Helpers.Segment) : Prop where
  addr : ctx.address_size = 64
  seg : ctx.seg_prefix_present = true → SegReady ctx.segment
  mode64 : ctx.is_mode64 = true
  segment : ctx.seg_prefix_present = false → ctx.segment = ds

/-- Without a segment prefix, `MoffsContext` gives `SegMoffsContext`. -/
theorem MoffsContext.toSeg {ctx : Instruction_Context} {ds : X86.Helpers.Segment}
    (h : MoffsContext ctx ds) : SegMoffsContext ctx ds :=
  ⟨h.addr, fun hs => absurd (h.seg.symm.trans hs) Bool.false_ne_true, h.mode64,
    fun _ => h.segment⟩

/-- `directMemoryOffset_run` with any segment prefix (`SegMoffsContext`): the segment returned is
`ctxSegment ctx false` (FS or GS after a segment prefix, else the flat data segment). -/
theorem directMemoryOffset_run_seg [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    (hds : s.DS = {userStackSegment with is_stack := some false})
    (ctx : Instruction_Context) (hctx : SegMoffsContext ctx s.DS)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (moffs : BitVec 64) (i : Nat) (hbytes : ∀ j < 8, bytes[i + j]? = some (immByte moffs j))
    (hlen : i + 8 ≤ bytes.length) (h15 : i + 8 ≤ 15) :
    (Direct_Memory_Offset 64 ctx (BitVec.add s.RIP (BitVec.ofNat 64 i))).run (afterFetches s k) =
      (.ok (ctxSegment ctx false, moffs, BitVec.add s.RIP (BitVec.ofNat 64 (i + 8))),
        afterFetches s (k + 8)) := by
  have hfetch := memFetch_run_of_bytesAt_imm64 s k h hcode hlow moffs i hbytes hlen h15
  have hlam := cpuidLAM_run (afterFetches s (k + 8))
    (reportsCPUFeature_of_sameControls (SameControls.afterFetches s (k + 8)) h.lam)
  have hges : Get_Effective_Segment ctx ctx.segment = .ok (ctxSegment ctx false) := by
    rw [getEffectiveSegment_run_eff ctx ctx.segment hctx.mode64]
    unfold effSegment ctxSegment
    cases hs : ctx.seg_prefix_present
    · rw [hctx.segment hs, hds]
      rfl
    · rfl
  unfold Direct_Memory_Offset
  simp only [hges]
  spec_run [
    Mem_Fetch => hfetch,
    CPUID_LAM => hlam]
  rw [← add_ofNat_add]
  have hv : BitVec.ofNat (Int.toNat 64) moffs.toNat = moffs := by
    rw [BitVec.ofNat_toNat]; exact BitVec.setWidth_eq moffs
  rw [hv]
  rfl

/-- `SegMoffsContext` at address size 32 (a `67` prefix): the offset is 4 bytes. -/
structure SegMoffsContext32 (ctx : Instruction_Context) (ds : X86.Helpers.Segment) : Prop where
  addr : ctx.address_size = 32
  seg : ctx.seg_prefix_present = true → SegReady ctx.segment
  mode64 : ctx.is_mode64 = true
  segment : ctx.seg_prefix_present = false → ctx.segment = ds

/-- `directMemoryOffset_run_seg` at address size 32 (a `67` prefix): the offset is the 4 bytes
`moffs` at offset `i`, zero-extended; LAM does not apply below address size 64. -/
theorem directMemoryOffset32_run_seg [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    (hds : s.DS = {userStackSegment with is_stack := some false})
    (ctx : Instruction_Context) (hctx : SegMoffsContext32 ctx s.DS)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (moffs : BitVec 32) (i : Nat) (hbytes : ∀ j < 4, bytes[i + j]? = some (immByte moffs j))
    (hlen : i + 4 ≤ bytes.length) (h15 : i + 4 ≤ 15) :
    (Direct_Memory_Offset 32 ctx (BitVec.add s.RIP (BitVec.ofNat 64 i))).run (afterFetches s k) =
      (.ok (ctxSegment ctx false, moffs.setWidth 64, BitVec.add s.RIP (BitVec.ofNat 64 (i + 4))),
        afterFetches s (k + 4)) := by
  have hfetch := memFetch_run_of_bytesAt_imm s k h hcode hlow 32 (by decide) moffs i hbytes hlen h15
  have hlam := cpuidLAM_run (afterFetches s (k + 4))
    (reportsCPUFeature_of_sameControls (SameControls.afterFetches s (k + 4)) h.lam)
  have hges : Get_Effective_Segment ctx ctx.segment = .ok (ctxSegment ctx false) := by
    rw [getEffectiveSegment_run_eff ctx ctx.segment hctx.mode64]
    unfold effSegment ctxSegment
    cases hs : ctx.seg_prefix_present
    · rw [hctx.segment hs, hds]
      rfl
    · rfl
  unfold Direct_Memory_Offset
  simp only [hges]
  spec_run [
    Mem_Fetch => hfetch,
    CPUID_LAM => hlam]
  rw [← add_ofNat_add]
  have hv : BitVec.ofNat (Int.toNat 64) moffs.toNat = moffs.setWidth 64 := BitVec.ofNat_toNat _ _
  rw [hv]
  rfl

/-- `Handle_RIP_Relative_Address` at address size 32 keeps a zero-extended 32-bit offset (a
`moffs` operand, never RIP-relative). -/
theorem handleRIPRelativeAddress32_zext_run (v : BitVec 32) (next : BitVec 64) :
    Handle_RIP_Relative_Address 32 false (v.setWidth 64) next = .ok (v.setWidth 64) := by
  rw [handleRIPRelativeAddress32_run]
  simp

/-- A register number below 4 needs no REX bit and its low bits are below 4. -/
theorem low4_spec : ∀ src : BitVec 4, src.toNat < 4 → regHigh src = 0 ∧ (regLow src).toNat < 4 := by
  decide

end X86Proofs
