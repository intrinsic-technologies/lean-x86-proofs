import X86Proofs.Step.Fetch

/-!
# Fetching an immediate

lean-x86's forms fetch their immediates with `Mem_Fetch ip n` (`MOV_GPRv_IMMv`, `MOV_GPRv_IMMz`,
the `alu` immediate forms, …); `memFetch_run_imm` (`Step/Fetch.lean`) is that fetch for any
bytes. This file states it for an immediate stored in the instruction:

- `immBytes n v`: the `n / 8` little-endian bytes of `v`; `immPartial_immByte`: assembling them
  gives back `v`.
- `memFetch_run_of_bytesAt_imm` (and `memFetch_run_of_bytesAt_imm32` / `memFetch_run_of_bytesAt_imm64` with the size an `Int`
  literal, as lean-x86's forms write it): the fetch of an immediate `v` stored as
  `immBytes n v` at offset `i` of the instruction returns `v`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-! ### Immediates as bytes -/

/-- Bit `k` of the value assembled from the first `j` bytes: bit `k % 8` of byte `k / 8`, or 0
above them. -/
theorem immPartial_getLsbD {n : Nat} (b : Nat → BitVec 8) (j k : Nat) (hk : k < n) :
    (immPartial b j : BitVec n).getLsbD k = (decide (k < 8 * j) && (b (k / 8)).getLsbD (k % 8)) := by
  induction j with
  | zero => simp [immPartial]
  | succ j ih =>
    rw [immPartial, getLsbD_setSlice _ _ _ _ _ hk, ih]
    split
    · rename_i h1
      rw [show k / 8 = j by omega, show k % 8 = k - 8 * j by omega]
      simp [show k < 8 * (j + 1) by omega]
    · rename_i h1
      by_cases h2 : k < 8 * j
      · simp [h2, show k < 8 * (j + 1) by omega]
      · simp [h2, show ¬ k < 8 * (j + 1) by omega]

/-- Byte `j` of `v` (bits `8 j` to `8 j + 7`). -/
def immByte {n : Nat} (v : BitVec n) (j : Nat) : UInt8 := UInt8.ofBitVec (v.extractLsb' (8 * j) 8)

/-- The `n / 8` bytes of `v`, little-endian: how an `n`-bit immediate is stored in an
instruction. -/
def immBytes (n : Nat) (v : BitVec n) : List UInt8 := (List.range (n / 8)).map (immByte v)

@[simp] theorem immBytes_length (n : Nat) (v : BitVec n) : (immBytes n v).length = n / 8 := by
  simp [immBytes]

theorem immBytes_getElem? {n : Nat} (v : BitVec n) {j : Nat} (hj : j < n / 8) :
    (immBytes n v)[j]? = some (immByte v j) := by
  simp [immBytes, List.getElem?_range hj]

/-- An immediate right after the bytes `pre`: its bytes are at offsets `pre.length + j`. -/
theorem immBytes_getElem?_append {n : Nat} (pre : List UInt8) (v : BitVec n) :
    ∀ j < n / 8, (pre ++ immBytes n v)[pre.length + j]? = some (immByte v j) := by
  intro j hj
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, immBytes_getElem? v hj]

/-- Assembling the bytes of `v` gives back `v` (for `n` a multiple of 8). -/
theorem immPartial_immByte {n : Nat} (hn : n % 8 = 0) (v : BitVec n) :
    immPartial (fun j => (immByte v j).toBitVec) (n / 8) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [immPartial_getLsbD _ _ _ hk]
  simp only [immByte, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb']
  simp [show k < 8 * (n / 8) by omega, show k % 8 < 8 by omega, show 8 * (k / 8) + k % 8 = k by omega]

/-- Offsets from `r` add up: `(r + i) + j = r + (i + j)`, in the `BitVec.add` spelling lean-x86's
address computations produce. -/
theorem add_ofNat_add (r : BitVec 64) (i j : Nat) :
    BitVec.add (BitVec.add r (BitVec.ofNat 64 i)) (BitVec.ofNat 64 j) =
      BitVec.add r (BitVec.ofNat 64 (i + j)) := by
  change r + BitVec.ofNat 64 i + BitVec.ofNat 64 j = r + BitVec.ofNat 64 (i + j)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]

theorem sub_add_ofNat (r : BitVec 64) (i : Nat) :
    BitVec.sub (BitVec.add r (BitVec.ofNat 64 i)) r = BitVec.ofNat 64 i := by
  change r + BitVec.ofNat 64 i - r = _
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/--
The fetch of an immediate. If the instruction's bytes are stored at RIP below 4 GiB and the
`n / 8` bytes at offset `i` (ending within the first 15) are the bytes of `v` (`immBytes n v`),
fetching `n` bits at RIP + `i` from a state after `k` fetches returns `v` and uses up `n / 8`
more fetches.
-/
theorem memFetch_run_of_bytesAt_imm [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n) (i : Nat)
    (hbytes : ∀ j < n / 8, bytes[i + j]? = some (immByte v j)) (hlen : i + n / 8 ≤ bytes.length)
    (h15 : i + n / 8 ≤ 15) :
    (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 i)) n).run (afterFetches s k) =
      (.ok v, afterFetches s (k + n / 8)) := by
  have hip (j : Nat) : BitVec.add (n := 64) s.RIP (BitVec.ofNat 64 i) + BitVec.ofNat 64 j =
      BitVec.add (n := 64) s.RIP (BitVec.ofNat 64 (i + j)) := add_ofNat_add s.RIP i j
  have hmn : n % 8 = 0 := by omega
  rw [memFetch_run_imm s k h n hn _ (immByte v) ?_ ?_ ?_, immPartial_immByte hmn]
  · rw [sub_add_ofNat]
    change (BitVec.ofNat 64 i + BitVec.ofNat 64 (n / 8)).toNat ≤ 15
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]
    omega
  · intro j hj
    rw [hip]
    exact code_address s.RIP hlow (by omega)
  · intro j hj
    rw [hip]
    have hl : i + j < bytes.length := by omega
    have := hcode (i + j) hl
    erw [this]
    have hb := hbytes j hj
    rw [List.getElem?_eq_getElem hl] at hb
    exact hb

/-- `memFetch_run_of_bytesAt_imm` for a 32-bit immediate, with the size written as lean-x86's forms write
it. -/
theorem memFetch_run_of_bytesAt_imm32 [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (v : BitVec 32) (i : Nat) (hbytes : ∀ j < 4, bytes[i + j]? = some (immByte v j))
    (hlen : i + 4 ≤ bytes.length) (h15 : i + 4 ≤ 15) :
    (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 i)) 32).run (afterFetches s k) =
      (.ok v, afterFetches s (k + 4)) :=
  memFetch_run_of_bytesAt_imm s k h hcode hlow 32 (by decide) v i hbytes hlen h15

/-- `memFetch_run_of_bytesAt_imm` for a 64-bit immediate. -/
theorem memFetch_run_of_bytesAt_imm64 [Bindings] (s : RamState) (k : Nat) (h : FetchReady s)
    {bytes : List UInt8} (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (v : BitVec 64) (i : Nat) (hbytes : ∀ j < 8, bytes[i + j]? = some (immByte v j))
    (hlen : i + 8 ≤ bytes.length) (h15 : i + 8 ≤ 15) :
    (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 i)) 64).run (afterFetches s k) =
      (.ok v, afterFetches s (k + 8)) :=
  memFetch_run_of_bytesAt_imm s k h hcode hlow 64 (by decide) v i hbytes hlen h15

/-- An 8-bit immediate is one byte. -/
theorem immBytes_eight (v : BitVec 8) : immBytes 8 v = [UInt8.ofBitVec v] := by
  simp [immBytes, immByte]

end X86Proofs
