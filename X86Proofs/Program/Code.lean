import X86Proofs.Step.Fetch

/-!
# Code in memory

A program's code is lean-x86's `X86.UserProcess.CodeMap`: a list of (address, byte) pairs, the
same type lean-x86's `Prelude.ImageSections.toCodeMap` produces from a program image. An
instruction or a contiguous block of code at `p` is `codeRange p bytes`, and code made of several
pieces is their concatenation.

`CodeIn code s`: every byte of `code` is stored in `s`'s memory at its address, and that address
lies below 4 GiB (the part the identity mapping covers). The bound is part of the placement: a
program proof states it once, where the program is loaded, and it never mentions RIP, so it is
not re-proved after each step. `CodeIn.bytesAt` and `CodeIn.low` turn a placed instruction into
the two hypotheses a step lemma takes (`BytesAt` and the code bound).

This is the one file that unfolds `codeRange` and `Prelude.userAddressLimit`; other files use
`codeRange_nil`, `codeRange_cons`, `userAddressLimit_eq` and the lemmas below.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- Every byte of `code` is stored in `s`'s memory at its address, and the address is below
4 GiB. -/
def CodeIn (code : CodeMap) (s : RamState) : Prop :=
  ∀ x ∈ code, x.1.toNat < Prelude.userAddressLimit ∧ s.external[x.1]? = some x.2

/-- `Prelude`'s user address limit is 4 GiB. -/
theorem userAddressLimit_eq : Prelude.userAddressLimit = 2^32 := rfl

/-- No bytes, no code. -/
theorem codeRange_nil (p : BitVec 64) : codeRange p [] = [] := rfl

/-- The first byte is at `p`, the rest from `p + 1`. -/
theorem codeRange_cons (p : BitVec 64) (b : UInt8) (bytes : List UInt8) :
    codeRange p (b :: bytes) = (p, b) :: codeRange (p + 1) bytes := rfl

theorem CodeIn.append_iff {a b : CodeMap} {s : RamState} :
    CodeIn (a ++ b) s ↔ CodeIn a s ∧ CodeIn b s := by
  simp only [CodeIn, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- Code in memory stays in memory if fewer bytes are asked for. -/
theorem CodeIn.mono {a b : CodeMap} {s : RamState} (hsub : ∀ x ∈ a, x ∈ b) (h : CodeIn b s) :
    CodeIn a s := fun x hx => h x (hsub x hx)

/-- `CodeIn` depends only on memory. -/
theorem CodeIn.of_external_eq {code : CodeMap} {s t : RamState} (he : t.external = s.external)
    (h : CodeIn code s) : CodeIn code t := by
  unfold CodeIn; rw [he]; exact h

/-- Byte `i` of `codeRange p bytes` is at `p + i`. -/
theorem mem_codeRange (p : BitVec 64) (bytes : List UInt8) (i : Nat) (hi : i < bytes.length) :
    (p + BitVec.ofNat 64 i, bytes[i]) ∈ codeRange p bytes := by
  induction bytes generalizing p i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [codeRange]
    | succ j =>
      simp only [codeRange, List.mem_cons, List.getElem_cons_succ]
      refine .inr ?_
      have := ih (p + 1) j (by simpa using hi)
      rwa [show p + 1 + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (j + 1) by
        rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]; rfl] at this

/-- Membership in `codeRange p bytes` records both the byte's index and its value: the entries
are `(p + i, bytes[i])`. -/
theorem mem_codeRange_iff (p : BitVec 64) (bytes : List UInt8) (x : BitVec 64 × UInt8) :
    x ∈ codeRange p bytes ↔ ∃ i : Fin bytes.length,
      x = (p + BitVec.ofNat 64 i.val, bytes[i.val]) := by
  induction bytes generalizing p with
  | nil => simp [codeRange]
  | cons b bs ih =>
    simp only [codeRange, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨⟨0, by simp⟩, by simp⟩
      · refine ⟨⟨i.val + 1, by simp [i.isLt]⟩, ?_⟩
        simp only [List.getElem_cons_succ, BitVec.ofNat_add, BitVec.add_assoc]
        rw [BitVec.add_comm (1 : BitVec 64)]
        rfl
    · rintro ⟨⟨i, hi⟩, rfl⟩
      cases i with
      | zero => exact .inl (by simp)
      | succ i =>
        refine .inr ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ?_⟩
        simp only [List.getElem_cons_succ, BitVec.ofNat_add,
          BitVec.add_assoc]
        rw [BitVec.add_comm (BitVec.ofNat 64 i)]
        rfl

/-- A byte of `codeRange p bytes` is at `p + j` for some `j` below the length. -/
theorem exists_of_mem_codeRange {p : BitVec 64} {bytes : List UInt8} {x : BitVec 64 × UInt8}
    (hx : x ∈ codeRange p bytes) : ∃ j < bytes.length, x.1 = p + BitVec.ofNat 64 j := by
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff p bytes x).mp hx
  exact ⟨i.val, i.isLt, rfl⟩

/-- A block of code splits into its first part and the rest right after it. -/
theorem codeRange_append (p : BitVec 64) (l₁ l₂ : List UInt8) :
    codeRange p (l₁ ++ l₂) =
      codeRange p l₁ ++ codeRange (p + BitVec.ofNat 64 l₁.length) l₂ := by
  induction l₁ generalizing p with
  | nil => simp [codeRange]
  | cons b bs ih =>
    simp only [List.cons_append, codeRange, ih, List.length_cons, List.cons.injEq, true_and]
    rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _)]
    rfl

/-- Bytes placed at `p` are stored at `p`. -/
theorem CodeIn.bytesAt {p : BitVec 64} {bytes : List UInt8} {s : RamState}
    (h : CodeIn (codeRange p bytes) s) : BytesAt s p bytes :=
  fun i hi => (h _ (mem_codeRange p bytes i hi)).2

/-- Bytes placed at `p` lie below 4 GiB, as a bound on `p` (the bound step lemmas take). -/
theorem CodeIn.low {p : BitVec 64} {bytes : List UInt8} {s : RamState}
    (h : CodeIn (codeRange p bytes) s) (hne : 0 < bytes.length) (hlen : bytes.length < 2^32) :
    p.toNat + bytes.length ≤ 2^32 := by
  have h0 := (h _ (mem_codeRange p bytes 0 hne)).1
  have hl := (h _ (mem_codeRange p bytes (bytes.length - 1) (by omega))).1
  simp only [Prelude.userAddressLimit, BitVec.toNat_add, BitVec.toNat_ofNat] at h0 hl
  rw [Nat.mod_eq_of_lt (a := bytes.length - 1) (by omega)] at hl
  have hp : p.toNat < 2^64 := p.isLt
  omega


/-! ### Code inside a block: an instruction's bytes inside the block's -/

theorem codeRange_mem_of_drop {p : BitVec 64} {all bytes : List UInt8} (off : Nat)
    (hsub : (all.drop off).take bytes.length = bytes) :
    ∀ x ∈ codeRange (p + BitVec.ofNat 64 off) bytes, x ∈ codeRange p all := by
  induction off generalizing p all with
  | zero =>
    simp only [List.drop_zero] at hsub
    intro x hx
    rw [show p + BitVec.ofNat 64 0 = p by simp] at hx
    rw [← List.take_append_drop bytes.length all, codeRange_append, hsub]
    exact List.mem_append_left _ hx
  | succ k ih =>
    cases all with
    | nil =>
      simp only [List.drop_nil, List.take_nil] at hsub
      subst hsub
      simp [codeRange]
    | cons b bs =>
      intro x hx
      simp only [List.drop_succ_cons] at hsub
      have := ih (p := p + 1) hsub x (by
        rwa [show p + 1 + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (k + 1) by
          apply BitVec.eq_of_toNat_eq
          simp
          omega])
      simp only [codeRange, List.mem_cons]
      exact .inr this

/-- The instruction at offset 0. -/
theorem codeRange_mem_of_take {p : BitVec 64} {all bytes : List UInt8}
    (hsub : all.take bytes.length = bytes) :
    ∀ x ∈ codeRange p bytes, x ∈ codeRange p all := by
  have := codeRange_mem_of_drop (p := p) (all := all) (bytes := bytes) 0 (by simpa using hsub)
  simpa using this

end X86Proofs
