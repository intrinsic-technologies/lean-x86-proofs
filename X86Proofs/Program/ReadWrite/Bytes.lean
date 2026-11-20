import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Bswap.Operation

/-!
# Byte windows

`Bytes m base len value`: the `len` bytes of memory `m` from `base` are all present, byte `i` with
value `value i`. A byte window connects machine loads and stores to an algorithm's arrays: a load
of a whole window reads the word its bytes make up (`Bytes.memLoad`, `Bytes.loadByte`), a store
updates the bytes it covers and keeps the rest (`Bytes.store`, `Bytes.writeByte`,
`Bytes.store_disjoint`), and windows split and join by offset (`Bytes.sub`, `Bytes.append`). A
stored value's bytes: `wordBytes`, a 64-bit word's eight; `storedByte_xor`; and
`storedByte_bswapSpec` (a byte-swapped word's bytes are the word's, big-endian).
-/

namespace X86Proofs
open X86 X86.Machine X86.UserProcess

/-- All bytes in a window are present and have the specified values. -/
def Bytes (m : Ram) (base : BitVec 64) (len : Nat) (value : Nat → UInt8) : Prop :=
  ∀ i < len, m[base + BitVec.ofNat 64 i]? = some (value i)

/-- Allocated bytes form a window of their own values. -/
theorem Bytes.of_isSome {m : Ram} {a : BitVec 64} {len : Nat}
    (h : ∀ i < len, (m[a + BitVec.ofNat 64 i]?).isSome) :
    Bytes m a len (fun i => memByte m (a + BitVec.ofNat 64 i)) := by
  intro i hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h i hi)
  change m[a + BitVec.ofNat 64 i]? = some ((m[a + BitVec.ofNat 64 i]?).getD 0)
  rw [hb]
  rfl

/-- A window's values matter only below its length. -/
theorem Bytes.congr {m : Ram} {a : BitVec 64} {len : Nat} {f g : Nat → UInt8}
    (h : Bytes m a len f) (he : ∀ i < len, f i = g i) : Bytes m a len g :=
  fun i hi => (h i hi).trans (congrArg some (he i hi))

/-- The `count` bytes from `offset` of a window form a window. -/
theorem Bytes.sub {m : Ram} {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    (h : Bytes m a len f) (offset count : Nat) (hb : offset + count ≤ len) :
    Bytes m (a + BitVec.ofNat 64 offset) count (fun i => f (offset + i)) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h (offset + i) (by omega)

/-- A copied byte window transports every specified subwindow of the source. -/
theorem Bytes.copy_sub {m m' : Ram} {src dst : BitVec 64} {count : Nat} {f : Nat → UInt8}
    (hs : Bytes m src count f) (hd : Bytes m' dst count f)
    (offset len : Nat) (hspan : offset + len ≤ count) {g : Nat → UInt8}
    (hb : Bytes m (src + BitVec.ofNat 64 offset) len g) :
    Bytes m' (dst + BitVec.ofNat 64 offset) len g := by
  apply (hd.sub offset len hspan).congr
  intro i hi
  exact Option.some.inj (((hs.sub offset len hspan) i hi).symm.trans (hb i hi))

/-- A window below 4 GiB is readable. -/
theorem Bytes.readable {s : RamState} {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    (h : Bytes s.external a len f) (hlow : a.toNat + len ≤ 2^32) :
    MemReadable s a len :=
  ⟨hlow, fun i hi => by rw [h i hi]; rfl⟩

/-- Reading an allocated window and splitting the result recovers its bytes. -/
theorem Bytes.of_memLoad {m : Ram} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n / 8, (m[a + BitVec.ofNat 64 i]?).isSome) :
    Bytes m a (n / 8) (storedByte (memLoad m a n)) := by
  apply (Bytes.of_isSome h).congr
  intro i hi
  exact (storedByte_memLoad m a i hi).symm

/-- Updating a subwindow preserves the bytes outside the write. -/
theorem Bytes.store {m : Ram} {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    (h : Bytes m a len f) (hlen : len ≤ 2^64) (offset : Nat) {n : Nat}
    (v : BitVec n) (hn : n ≤ 128) (hb : offset + n / 8 ≤ len) :
    Bytes (memStore m (a + BitVec.ofNat 64 offset) v) a len
      (fun i => if offset ≤ i ∧ i < offset + n / 8 then storedByte v (i - offset) else f i) := by
  intro i hi
  dsimp only
  by_cases hin : offset ≤ i ∧ i < offset + n / 8
  · rw [ite_eq_left hin]
    have he : a + BitVec.ofNat 64 i =
        a + BitVec.ofNat 64 offset + BitVec.ofNat 64 (i - offset) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    rw [he]
    exact memStore_getElem?_self m _ v hn _ (by omega)
  · rw [ite_eq_right hin, memStore_getElem?_of_ne]
    · exact h i hi
    · intro j hj he
      have he' : BitVec.ofNat 64 i = BitVec.ofNat 64 (offset + j) := by
        apply (BitVec.add_right_inj a).mp
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he.symm
      have := congrArg BitVec.toNat he'
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega

/-- A store outside a byte window preserves that window. -/
theorem Bytes.store_disjoint {m : Ram} {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    (h : Bytes m a len f) (addr : BitVec 64) {n : Nat} (v : BitVec n)
    (ha : RangeApart addr (n / 8) a len) : Bytes (memStore m addr v) a len f := by
  intro i hi
  rw [memStore_getElem?_of_ne m addr v _ (fun j hj => ha j hj i hi)]
  exact h i hi

/-- A frame agreement transports every byte outside the allowed effects. -/
theorem Bytes.of_agreesExcept {s t : RamState} {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    {cs : List Component} (h : Bytes s.external a len f) (he : AgreesExcept cs s t)
    (ha : ∀ i < len, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    Bytes t.external a len f := fun i hi => (he.byte (ha i hi)).trans (h i hi)

/-- A store of an `n`-bit value makes its `n / 8` bytes a window of the value's bytes. -/
theorem Bytes.store_self (m : Ram) (a : BitVec 64) {n : Nat} (v : BitVec n) (hn : n ≤ 128) :
    Bytes (memStore m a v) a (n / 8) (storedByte v) :=
  fun i hi => memStore_getElem?_self m a v hn i hi

/-- Two adjacent windows join into one. -/
theorem Bytes.append {m : Ram} {a : BitVec 64} {len count : Nat} {f g : Nat → UInt8}
    (h : Bytes m a len f) (h' : Bytes m (a + BitVec.ofNat 64 len) count g) :
    Bytes m a (len + count) (fun i => if i < len then f i else g (i - len)) := by
  intro i hi
  dsimp only
  by_cases hil : i < len
  · rw [ite_eq_left hil]; exact h i hil
  · rw [ite_eq_right hil]
    have he : a + BitVec.ofNat 64 i =
        a + BitVec.ofNat 64 len + BitVec.ofNat 64 (i - len) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
    rw [he]
    exact h' (i - len) (by omega)

/-- Disjoint offsets in a common window give disjoint machine address ranges. -/
theorem RangeApart.offsets (base : BitVec 64) {a b len count : Nat}
    (ha : a + len ≤ 2^64) (hb : b + count ≤ 2^64)
    (hab : a + len ≤ b ∨ b + count ≤ a) :
    RangeApart (base + BitVec.ofNat 64 a) len (base + BitVec.ofNat 64 b) count := by
  intro i hi j hj he
  have he' : BitVec.ofNat 64 (a + i) = BitVec.ofNat 64 (b + j) := by
    apply (BitVec.add_right_inj base).mp
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he
  have := congrArg BitVec.toNat he'
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- A store immediately after a known prefix extends that prefix. -/
theorem Bytes.append_store {m : Ram} {a : BitVec 64} {len : Nat} {f : Nat → UInt8}
    (h : Bytes m a len f) {n : Nat} (v : BitVec n) (hn : n ≤ 128)
    (hbound : len + n / 8 ≤ 2^64) (hv : ∀ i < n / 8, storedByte v i = f (len + i)) :
    Bytes (memStore m (a + BitVec.ofNat 64 len) v) a (len + n / 8) f := by
  have ha : RangeApart (a + BitVec.ofNat 64 len) (n / 8) a len := by
    simpa only [BitVec.add_zero] using RangeApart.offsets a
      (a := len) (len := n / 8) (b := 0) (count := len)
      hbound (by omega) (.inr (by omega))
  have hp := h.store_disjoint _ v ha
  have hs := Bytes.store_self m (a + BitVec.ofNat 64 len) v hn
  apply (hp.append hs).congr
  intro i hi
  by_cases hil : i < len
  · simp only [hil, ite_true]
  · simp only [hil, ite_false]
    rw [hv (i - len) (by omega), Nat.add_sub_cancel' (by omega)]

/-- The user-process return reader agrees with a complete eight-byte word window. -/
theorem Bytes.loadBytes64 {m : Ram} {a : BitVec 64} {v : BitVec 64}
    (h : Bytes m a 8 (storedByte v)) : Machine.loadBytes m a 8 = .ok v := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  simp only [BitVec.add_zero] at h0
  simp only [Machine.loadBytes, Machine.loadBytes.loop, addAddress, fromNat,
    BitVec.add_zero, Nat.zero_add, Nat.reduceAdd, h0, h1, h2, h3, h4, h5, h6, h7,
    Nat.pow_zero, Nat.mul_one, Nat.reducePow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [storedByte, UInt8.toNat_ofNat',
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow]
  have := v.isLt
  omega

/-- Byte `i` of a stored value is bits `8i` to `8i + 7` of it. -/
theorem storedByte_eq_extract {n : Nat} (v : BitVec n) (i : Nat) :
    storedByte v i = UInt8.ofBitVec (v.extractLsb' (8 * i) 8) := rfl

/-- A value whose width is a multiple of 8 is determined by its bytes. -/
theorem storedByte_injective {n : Nat} (hn : n % 8 = 0) {x y : BitVec n}
    (h : ∀ i < n / 8, storedByte x i = storedByte y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have he := congrArg (fun b : UInt8 => b.toBitVec.getLsbD (k % 8)) (h (k / 8) (by omega))
  simpa only [storedByte_eq_extract, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb',
    show k % 8 < 8 by omega, decide_true, Bool.true_and,
    show 8 * (k / 8) + k % 8 = k by omega] using he

/-- An `n`-bit load of a window of the bytes of `v` reads `v`. -/
theorem Bytes.memLoad {m : Ram} {a : BitVec 64} {n : Nat} {v : BitVec n}
    (h : Bytes m a (n / 8) (storedByte v)) (hn : n % 8 = 0) (h128 : n ≤ 128) :
    memLoad m a n = v := by
  have hb := Bytes.store_self m a v h128
  calc
    X86Proofs.memLoad m a n = X86Proofs.memLoad (memStore m a v) a n := by
      apply memLoad_congr
      intro i hi
      change (m[a + BitVec.ofNat 64 i]?).getD 0 =
        ((memStore m a v)[a + BitVec.ofNat 64 i]?).getD 0
      rw [h i hi, hb i hi]
    _ = v := memLoad_memStore m a hn h128 v

/-- The eight bytes of a 64-bit word, little-endian: what memory holding it holds. -/
def wordBytes (v : BitVec 64) : List UInt8 := List.ofFn fun i : Fin 8 => storedByte v i

/-- Each byte of an XOR is the XOR of the bytes. -/
theorem storedByte_xor {n : Nat} (x y : BitVec n) (i : Nat) :
    storedByte (x ^^^ y) i = storedByte x i ^^^ storedByte y i := by
  apply UInt8.eq_of_toBitVec_eq
  simp [storedByte_eq_extract, BitVec.extractLsb'_xor]

/-- Byte `i` of a byte-swapped value is byte `n / 8 - 1 - i` of the value: a `bswap`'d word
stored (little-endian) holds the word's bytes big-endian. -/
theorem storedByte_bswapSpec {n : Nat} (x : BitVec n) {i : Nat} (hi : i < n / 8) :
    storedByte (bswapSpec x) i = storedByte x (n / 8 - 1 - i) := by
  rw [storedByte_eq_extract, storedByte_eq_extract, Nat.mul_comm 8 i,
    Nat.mul_comm 8 (n / 8 - 1 - i)]
  change UInt8.ofBitVec (lane 8 (bswapSpec x) i) = UInt8.ofBitVec (lane 8 x (n / 8 - 1 - i))
  rw [bswapSpec, lane_ofLanes _ _ hi]

/-- A one-byte machine load reads the corresponding byte of a window. -/
theorem Bytes.loadByte {m : Ram} {base : BitVec 64} {len : Nat} {bytes : Nat → UInt8}
    (h : Bytes m base len bytes) (offset : Nat) (hoffset : offset < len) :
    X86Proofs.memLoad m (base + BitVec.ofNat 64 offset) 8 = (bytes offset).toBitVec := by
  apply Bytes.memLoad (n := 8) (v := (bytes offset).toBitVec) ?_ (by decide) (by decide)
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simpa [storedByte] using h offset hoffset

/-- A one-byte store changes precisely one entry of a byte window. -/
theorem Bytes.writeByte {m : Ram} {base : BitVec 64} {len : Nat} {bytes : Nat → UInt8}
    (h : Bytes m base len bytes) (hlen : len ≤ 2^64)
    (offset : Nat) (hoffset : offset < len) (value : UInt8) :
    Bytes (memStore m (base + BitVec.ofNat 64 offset) value.toBitVec) base len
      (fun i => if i = offset then value else bytes i) := by
  apply (h.store hlen offset value.toBitVec (by decide) (by omega)).congr
  intro i _
  have he : (offset ≤ i ∧ i < offset + 8 / 8) ↔ i = offset := by omega
  simp only [he]
  by_cases hi : i = offset
  · subst i; simp [storedByte]
  · simp [hi]

end X86Proofs

