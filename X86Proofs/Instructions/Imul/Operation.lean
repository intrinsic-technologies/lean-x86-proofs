import X86Proofs.Core.Shift
import X86Proofs.Core.Bits
import X86Proofs.Program.ReadWrite.WritePair

/-!
# IMUL specification

Signed multiply, in two shapes (lean-x86's `IMUL_DOUBLE` and `IMUL_SINGLE`):

- One operand (`F7 /5`, `F6 /5`): `RDX:RAX ← RAX ∗ SRC` (`EDX:EAX ← EAX ∗ SRC`, `DX:AX ← AX ∗ SRC`;
  `AX ← AL ∗ SRC` at 8 bits), the full signed `2n`-bit product. `imulWideResult` gives its low
  half (RAX, or AL) and high half (RDX, or AH): the product's two's-complement bits `0 … n - 1` and
  `n … 2n - 1` (`p / 2 ^ n` rounds down, so the high half is the arithmetic shift). CF and OF are
  set when the product is not the sign extension of its low half, cleared otherwise.
- Two and three operands (`0F AF`, `6B`, `69`): `DEST ← TruncateToOperandSize(SRC1 ∗ SRC2)`. CF and
  OF are set when the signed value of the truncated result is not the product (significant bits
  were lost), cleared otherwise (`imulSpec`).

In both, SF, ZF, AF and PF are undefined: lean-x86 draws them from its oracle in the order SF, ZF,
AF, PF, and the specs take them as `u 0`, `u 1`, `u 2`, `u 3`. `imulWideFlags` and `imulFlags` are
the same as `StatusFlagsOutcome`s, the undefined flags `none`. The truncated product is the
product (`ofInt_toInt_mul`, `Core/Bits.lean`).
-/

namespace X86Proofs

/-- The signed `2n`-bit product of `x` and `y`, as (low half, high half). -/
def imulWideResult {n : Nat} (x y : BitVec n) : BitVec n × BitVec n :=
  let p := x.toInt * y.toInt
  (BitVec.ofInt n p, BitVec.ofInt n (p / 2 ^ n))

/-- CF and OF of the one-operand IMUL: the product is not the sign extension of its low half. -/
def imulWideCarry {n : Nat} (x y : BitVec n) : Bool :=
  let p := x.toInt * y.toInt
  (BitVec.ofInt n p).signExtend (n + n) != BitVec.ofInt (n + n) p

/-- Result and flags of the one-operand IMUL: the low and high halves of `x ∗ y` and the flags,
with `u` the unspecified bits for SF, ZF, AF, PF (in that order). -/
def imulWideSpec {n : Nat} (u : Nat → Bool) (x y : BitVec n) :
    BitVec n × BitVec n × StatusFlags :=
  let r := imulWideResult x y
  let c := imulWideCarry x y
  (r.1, r.2, { CF := c, OF := c, SF := u 0, ZF := u 1, AF := u 2, PF := u 3 })

/-- What the one-operand IMUL does to the flags: CF and OF from `imulWideCarry`; SF, ZF, AF and PF
are undefined. -/
def imulWideFlags {n : Nat} (x y : BitVec n) : StatusFlagsOutcome :=
  let c := imulWideCarry x y
  { CF := some c, OF := some c, SF := none, ZF := none, AF := none, PF := none }

theorem imulWideFlags_allows {n : Nat} (u : Nat → Bool) (x y : BitVec n) :
    (imulWideFlags x y).Allows (imulWideSpec u x y).2.2 :=
  ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

/-- Result and flags of the two- and three-operand IMUL: `x ∗ y` truncated to `n` bits, CF and OF
set when that loses significant bits, and `u` the unspecified bits for SF, ZF, AF, PF. -/
def imulSpec {n : Nat} (u : Nat → Bool) (x y : BitVec n) : BitVec n × StatusFlags :=
  let p := x.toInt * y.toInt
  let r := BitVec.ofInt n p
  let c := r.toInt != p
  (r, { CF := c, OF := c, SF := u 0, ZF := u 1, AF := u 2, PF := u 3 })

/-- What the two- and three-operand IMUL does to the flags: CF and OF say the truncated product
is not the product; SF, ZF, AF and PF are undefined. -/
def imulFlags {n : Nat} (x y : BitVec n) : StatusFlagsOutcome :=
  let p := x.toInt * y.toInt
  let c := (BitVec.ofInt n p).toInt != p
  { CF := some c, OF := some c, SF := none, ZF := none, AF := none, PF := none }

theorem imulFlags_allows {n : Nat} (u : Nat → Bool) (x y : BitVec n) :
    (imulFlags x y).Allows (imulSpec u x y).2 :=
  ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

open X86 X86.Helpers

theorem imul_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 16 ∨ n = 32 ∨ n = 64)
    (x y : BitVec n) :
    (X86.Instructions.Operations.IMUL_SINGLE n x y).run s =
      let r := imulSpec (fun i => oracleBit (oracleSkip s.oracle i)) x y
      (.ok r.1, setFlags { s with oracle := oracleSkip s.oracle 4 } r.2) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.IMUL_SINGLE
    simp only [x86_runtime, Int.pow_zero, Int.ediv_one]
    repeat spec_bind_rfl
    simp only [imulSpec]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem ofInt_hi_append_lo8 (P : Int) :
    BitVec.ofInt 8 (P / 2 ^ 8) ++ BitVec.ofInt 8 P = BitVec.ofInt 16 P := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofInt]
  omega

theorem imulWideCarry_bit {n : Nat} (m : Nat) (hm : m = n + n) (x y : BitVec n) :
    (if (BitVec.ofInt m (BitVec.ofInt n (x.toInt * y.toInt)).toInt ==
        BitVec.ofInt m (x.toInt * y.toInt)) = true then (0 : X86.Runtime.Bit) else 1) =
      BitVec.ofBool (imulWideCarry x y) := by
  subst hm
  show _ = BitVec.ofBool (BitVec.ofInt (n + n) (BitVec.ofInt n (x.toInt * y.toInt)).toInt !=
    BitVec.ofInt (n + n) (x.toInt * y.toInt))
  generalize BitVec.ofInt (n + n) (BitVec.ofInt n (x.toInt * y.toInt)).toInt = A
  generalize BitVec.ofInt (n + n) (x.toInt * y.toInt) = B
  cases h : (A == B) <;> simp [bne, h] <;> rfl

theorem imul_wide_operation {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (n : Nat)
    (hn : n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (X86.Instructions.Operations.IMUL_DOUBLE n x).run s =
      let r := imulWideSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand n).read s) x
      (.ok (), (Operand.reg 2 : Operand n).write ((Operand.reg 0 : Operand n).write
        (setFlags { s with oracle := oracleSkip s.oracle 4 } r.2.2) r.1) r.2.1) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.IMUL_DOUBLE
    simp only [x86_runtime]
    spec_bind_rfl
    spec_bind_with raxLow_run s _ (by decide)
    simp only [Int.reduceToNat, Int.pow_zero, Int.ediv_one]
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with rax_run _
    spec_bind_with liftM_mergeGPR_run _ _ (by decide) _ _
    spec_bind_with raxWrite_run _ _
    spec_bind_with rdx_run _
    spec_bind_with liftM_mergeGPR_run _ _ (by decide) _ _
    spec_bind_with rdxWrite_run _ _
    rw [← Operand.write_reg_eq_set, ← Operand.write_reg_eq_set]
    simp only [Operand.write_write_setFlags]
    simp only [imulWideSpec, imulWideResult, Operand.read_reg64, Operand.read_reg32,
      Operand.read_reg16, BitVec.setWidth_eq, Int.reduceToNat]
    generalize hT : (Operand.reg 2 : Operand _).write ((Operand.reg 0 : Operand _).write s _) _ = T
    have hTo : s.oracle = T.oracle := by subst hT; rfl
    repeat spec_bind_rfl
    rw [rflagsSetCF_run]
    dsimp only
    simp only [hTo, Int.reduceToNat]
    simp (disch := decide) only [imulWideCarry_bit]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem imul_wide_operation8 {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (x : BitVec 8) :
    (X86.Instructions.Operations.IMUL_DOUBLE 8 x).run s =
      let r := imulWideSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand 8).read s) x
      (.ok (), (Operand.reg 0 : Operand 16).write
        (setFlags { s with oracle := oracleSkip s.oracle 4 } r.2.2) (r.2.1 ++ r.1)) := by
  unfold X86.Instructions.Operations.IMUL_DOUBLE
  simp only [x86_runtime]
  spec_bind_rfl
  spec_bind_with raxLow_run s _ (by decide)
  simp only [Int.reduceToNat, sliceInclusive_eq, Int.reduceSub, Int.reduceAdd,
    x86_runtime, Int.pow_zero, Int.ediv_one]
  spec_bind_rfl
  spec_bind_with axWrite_run _ _
  rw [← Operand.write_reg_eq_set]
  simp only [Operand.write_setFlags]
  simp only [imulWideSpec, imulWideResult, ofInt_hi_append_lo8]
  simp only [Operand.read_reg8, Int.reduceToNat]
  generalize hT : (Operand.reg 0 : Operand 16).write s _ = T
  have hTo : s.oracle = T.oracle := by subst hT; rfl
  repeat spec_bind_rfl
  rw [rflagsSetCF_run]
  dsimp only
  simp only [hTo, Int.reduceToNat]
  simp (disch := decide) only [imulWideCarry_bit]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

attribute [x86_compose] imulWideFlags imulFlags

end X86Proofs
