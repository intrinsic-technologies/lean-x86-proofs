import X86

/-!
# The oracle

lean-x86 draws every value Intel leaves unspecified (an undefined flag, a translation's cached
fields) from the state's oracle, a stream of bits with a read position and an optional `limit`
(bits at or after it read as false). `oracleBit` is the next bit, `oracleSkip o n` the oracle
after `n` bits are used up, and `oracleTakeCount o n` counts the bits read before the limit.
`oracleTake_one`, `oracleTake_fst` and `oracleTake_snd` describe `Oracle.take` in those terms;
other files use these lemmas rather than unfolding `Oracle.take`.
`oracleTake_match_eq_oracleTakeCount` relates the matcher Lean generates for `Oracle.take`
(`Oracle.take.match_1`) to `oracleTakeCount`; it is the only statement that names the matcher.
-/

namespace X86Proofs

open X86

/-- The next unspecified bit the oracle supplies: the bit at its position, or false at or after
its `limit`. -/
def oracleBit (o : X86.Runtime.Oracle) : Bool :=
  match o.limit with
  | some limit => if o.position < limit then o.bits o.position else false
  | none => o.bits o.position

/-- The oracle after `n` bits are used up. -/
def oracleSkip (o : X86.Runtime.Oracle) (n : Nat) : X86.Runtime.Oracle :=
  { o with position := o.position + n }

/-- The number of bits `Oracle.take n` reads before `limit`. -/
def oracleTakeCount (o : X86.Runtime.Oracle) (n : Nat) : Nat :=
  match o.limit with
  | some limit => min n (limit - o.position)
  | none => n

/-- Bridge lean-x86's internal bit-count matcher to `oracleTakeCount`. -/
theorem oracleTake_match_eq_oracleTakeCount (o : X86.Runtime.Oracle) (n : Nat) :
    X86.Runtime.Oracle.take.match_1 (fun _ => Nat) o.limit
      (fun limit => min n (limit - o.position)) (fun _ => n) = oracleTakeCount o n := rfl

/-- Using up no oracle bits leaves the oracle as it is. -/
@[simp] theorem oracleSkip_zero (o : X86.Runtime.Oracle) : oracleSkip o 0 = o := by
  simp [oracleSkip]

/-- `Oracle.take 1` returns `oracleBit` and uses up one bit. -/
theorem oracleTake_one (o : X86.Runtime.Oracle) :
    o.take 1 = (BitVec.ofBool (oracleBit o), oracleSkip o 1) := by
  unfold X86.Runtime.Oracle.take oracleBit oracleSkip
  cases hl : o.limit with
  | none => cases hb : o.bits o.position <;> simp [hb, X86.Runtime.Oracle.take.go]
  | some limit =>
    by_cases h : o.position < limit
    · have hn : min 1 (limit - o.position) = 1 := by omega
      cases hb : o.bits o.position <;> simp [hb, h, hn, X86.Runtime.Oracle.take.go]
    · have hn : min 1 (limit - o.position) = 0 := by omega
      simp [h, hn, X86.Runtime.Oracle.take.go]

/-- The single bit `Oracle.take 1` assembles from `oracleTakeCount o 1` bits is `oracleBit`. -/
theorem oracleTakeGo_one (o : X86.Runtime.Oracle) :
    BitVec.ofNat 1 (X86.Runtime.Oracle.take.go o (oracleTakeCount o 1) 0 0) =
      BitVec.ofBool (oracleBit o) :=
  congrArg Prod.fst (oracleTake_one o)

/-- The `n` bits `Oracle.take n` returns, assembled from `oracleTakeCount o n` bits.
An operation that draws an unspecified multi-bit value, e.g. SHLD's result for a count above the
operand size, reaches this form. -/
theorem oracleTake_fst (o : X86.Runtime.Oracle) (n : Nat) :
    (o.take n).1 = BitVec.ofNat n (X86.Runtime.Oracle.take.go o (oracleTakeCount o n) 0 0) := rfl

/-- `Oracle.take n` uses up `n` bits. -/
theorem oracleTake_snd (o : X86.Runtime.Oracle) (n : Nat) : (o.take n).2 = oracleSkip o n := rfl

theorem oracleSkip_oracleSkip (o : X86.Runtime.Oracle) (a b : Nat) :
    oracleSkip (oracleSkip o a) b = oracleSkip o (a + b) := by
  simp [oracleSkip, Nat.add_assoc]

end X86Proofs
