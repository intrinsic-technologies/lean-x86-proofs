import X86Proofs.Step.ReadyToStep
import X86Proofs.Program.Code
import Prelude.ImageSections
import Prelude.Bytes.Utf8

/-!
# Entry point: from a program's starting state to the library's assumptions

The library's triples assume `ReadyToStep s`, `Prelude.SupportedSSE Bindings.processor s` (SSE
triples) and `CodeIn code s` for the code they run. A program theorem states its starting state
with lean-x86's `Prelude` predicates, for bindings it takes as a parameter (lean-x86 has no
production `Bindings` instance; `Prelude`'s predicates take the selected bindings):

- `Prelude.SupportedIntegerMachineState bindings.processor s`,
- `Prelude.SMRRUnblocked bindings s` and `Prelude.WriteBackMemoryType bindings s 0`: these read
  the live SMRR, MTRR and PAT registers, so they are hypotheses on the starting state, not facts
  about the bindings,
- that the image is in memory (`∀ address byte, (address, byte) ∈ image → s.external[address]? =
  some byte`).

`EntryReady.of_supported` turns these into `EntryReady code s` (all three of the library's
assumptions). It needs two more facts:

- **The decoder's LZCNT query is answered** (`hlzcnt`). Every generated decoder reads six CPUID
  features. Five follow from `SupportedIntegerMachineState` (`DecoderFeatures.of_supported`):
  MMX, SSE, SSE2 and CMPXCHG16B share CPUID leaf 1 with the SSE report of `SupportedSSE`, and
  CET_SS (leaf 7, subleaf 0) is answered whenever the LAM report of `SupportedIntegerCPU`
  (leaf 7, subleaf 1) is. LZCNT is leaf `0x80000001`, which no `Prelude` predicate queries, and the
  processor's CPUID query may fail on it, so it stays a hypothesis.
- **The image lies below 4 GiB** (`CodeLow code`; for an image as `Prelude.ImageSections`,
  `SectionsLow`, which is decidable, one comparison per section).

A program proof uses it like this:

```lean
theorem program_spec (bindings : Machine.Bindings) (hsmrr : SMRRUnblocked bindings s) … :=
  letI := bindings
  have e := EntryReady.of_sections hMachine hsmrr hmt hlzcnt hLoaded (by decide)
  -- e.ready : ReadyToStep s, e.sse : SupportedSSE …, e.code : CodeIn programSections.toCodeMap s
  -- the code of one function or instruction, `k` bytes into section `sec`:
  have hf := e.code.slice_of_section hsec k n (by decide)
  …
```

`CodeIn.slice_of_section` gives `CodeIn (codeRange (sec.address + k) (sec.bytes.toListFrom k n))`;
`sec.bytes.toListFrom k n` evaluates to the literal bytes by `rfl` or `decide`, and
`CodeIn.mono` moves to any sub-list of placed code. `toListFrom` looks a chunk up for every byte,
by walking the chunk list, so far into a large section `chunked_toListFrom_eq_read` is the cheaper
route: `chunkedRead` looks up each chunk the bytes span once. For an image built with `codeRange`,
`codeLow_codeRange` and `CodeLow.append` give the bound, and `codeRange_slice_subset` restricts.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-! ### CPUID: the decoder's features from `Prelude`'s reports

The CPUID facts (`reportsCPUFeature_of_sameLeaf`, `reportsCETSS_of_reportsLAM`) are
`Core/ReadOnly.lean`'s. -/

/--
The decoder's CPUID features from `SupportedIntegerMachineState` and the one it doesn't cover:
LZCNT (leaf `0x80000001`).
-/
theorem DecoderFeatures.of_supported [Bindings] {s : RamState}
    (h : Prelude.SupportedIntegerMachineState Bindings.processor s)
    (hlzcnt : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding b) :
    DecoderFeatures s :=
  have sse := h.sse.feature
  ⟨hlzcnt, reportsCPUFeature_of_sameLeaf (f := CPUID_SSE_Encoding) rfl rfl sse, ⟨true, sse⟩,
    reportsCPUFeature_of_sameLeaf (f := CPUID_SSE_Encoding) rfl rfl sse, reportsCETSS_of_reportsLAM h.integer.lam,
    reportsCPUFeature_of_sameLeaf (f := CPUID_SSE_Encoding) rfl rfl sse⟩

/-! ### SMRR -/

/--
A sufficient condition for `Prelude.SMRRUnblocked`, for any bindings: the SMRR mask's valid bit
(bit 11) is clear. lean-x86's user-process profile sets the mask to 0.
-/
theorem smrrUnblocked_of_mask_invalid {σ : Type} (b : Bindings) (s : X86.State σ)
    (h : s.IA32_SMRR_PHYSMASK.getLsbD 11 = false) : Prelude.SMRRUnblocked b s := by
  intro address
  unfold X86.Helpers.Emulate_Memory.SMRR_Matches
  have hm : (BitVec.extractLsb' 11 1 s.IA32_SMRR_PHYSMASK) = 0#1 := by
    ext i hi
    have : i = 0 := by omega
    subst this; simpa using h
  simp [Runtime.CheckedSlice.read, x86_runtime, hm, bind, Except.bind, pure, Except.pure]
  generalize (_ == 0#1) = c
  intro hc
  cases c <;> exact absurd hc (by decide)

/-! ### Code: the image in memory, below 4 GiB -/

/-- Every address of `code` is below 4 GiB. -/
def CodeLow (code : CodeMap) : Prop :=
  ∀ x ∈ code, x.1.toNat < Prelude.userAddressLimit

theorem CodeLow.append {a b : CodeMap} (ha : CodeLow a) (hb : CodeLow b) : CodeLow (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

/-- An image in memory and below 4 GiB is `CodeIn`. -/
theorem CodeIn.of_loaded {code : CodeMap} {s : RamState}
    (hloaded : ∀ address byte, (address, byte) ∈ code → s.external[address]? = some byte)
    (hlow : CodeLow code) : CodeIn code s :=
  fun x hx => ⟨hlow x hx, hloaded x.1 x.2 hx⟩

/-- Bytes placed at `p` that end at or below 4 GiB are below 4 GiB. -/
theorem codeLow_codeRange {p : BitVec 64} {bytes : List UInt8}
    (h : p.toNat + bytes.length ≤ Prelude.userAddressLimit) : CodeLow (codeRange p bytes) := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := exists_of_mem_codeRange hx
  rw [hx, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [userAddressLimit_eq] at *
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `n` bytes from offset `k` of a block of code are part of it. -/
theorem codeRange_slice_subset (base : BitVec 64) (l : List UInt8) (k n : Nat) :
    ∀ x ∈ codeRange (base + BitVec.ofNat 64 k) ((l.drop k).take n), x ∈ codeRange base l := by
  intro x hx
  by_cases hk : k ≤ l.length
  · have e1 := codeRange_append base (l.take k) (l.drop k)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at e1
    have e2 := codeRange_append (base + BitVec.ofNat 64 k) ((l.drop k).take n)
      ((l.drop k).drop n)
    rw [List.take_append_drop] at e2
    rw [e1]
    exact List.mem_append_right _ (e2 ▸ List.mem_append_left _ hx)
  · rw [List.drop_eq_nil_of_le (by omega)] at hx
    simp [codeRange_nil] at hx

/-! ### Images as `Prelude.ImageSections` -/

/-- Every section of the image ends at or below 4 GiB. Decidable: one comparison per section. -/
def SectionsLow (sections : Prelude.ImageSections) : Prop :=
  ∀ sec ∈ sections, sec.address.toNat + sec.bytes.size ≤ Prelude.userAddressLimit

instance (sections : Prelude.ImageSections) : Decidable (SectionsLow sections) :=
  inferInstanceAs (Decidable (∀ sec ∈ sections, _))

theorem chunked_toList_length (d : Prelude.Bytes.Chunked) : d.toList.length = d.size := by
  simp [Prelude.Bytes.Chunked.toList, Prelude.Bytes.Chunked.toListFrom]

theorem chunked_toListFrom_length (d : Prelude.Bytes.Chunked) (k n : Nat) :
    (d.toListFrom k n).length = n := by
  simp [Prelude.Bytes.Chunked.toListFrom]

theorem SectionsLow.codeLow {sections : Prelude.ImageSections}
    (h : SectionsLow sections) : CodeLow sections.toCodeMap := by
  intro x hx
  obtain ⟨sec, hsec, hx⟩ := List.mem_flatMap.1 hx
  have hs := h sec hsec
  rw [← chunked_toList_length] at hs
  exact codeLow_codeRange hs x hx

private theorem take_range' (s n k : Nat) : (List.range' s n).take k = List.range' s (min k n) := by
  induction n generalizing s k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.range'_succ, ih, Nat.succ_min_succ]

/-- `n` bytes from offset `k` of a section, as `toListFrom` (which evaluates cheaply). -/
theorem chunked_toList_slice (d : Prelude.Bytes.Chunked) (k n : Nat) (h : k + n ≤ d.size) :
    (d.toList.drop k).take n = d.toListFrom k n := by
  simp only [Prelude.Bytes.Chunked.toList, Prelude.Bytes.Chunked.toListFrom]
  rw [← List.map_drop, ← List.map_take, List.drop_range', take_range']
  congr 2
  · simp
  · omega

/-- `count` bytes of `d` from `start`, at most a chunk's size: those in the first byte's chunk, then
those in the next, each run read with one chunk lookup and one shift (`chunked_toListFrom_eq_read`).
A lookup walks the chunk list, so its kernel cost grows with the chunk's index (about 23 ms for the
last of 1,024, the most a section has, from 8 MiB on): `toListFrom` pays it for every byte, this
once or twice per read. -/
def chunkedRead (d : Prelude.Bytes.Chunked) (start count : Nat) : List UInt8 :=
  let p := d.base + start
  let k := p % d.chunkSize
  let m := min count (d.chunkSize - k)
  Prelude.Bytes.bytesLE m ((d.chunk (p / d.chunkSize) >>> (8 * k)) % 2 ^ (8 * m)) ++
    Prelude.Bytes.bytesLE (count - m) (d.chunk (p / d.chunkSize + 1) % 2 ^ (8 * (count - m)))

private theorem bytesLE_mod (n v : Nat) :
    Prelude.Bytes.bytesLE n (v % 2 ^ (8 * n)) = Prelude.Bytes.bytesLE n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [Prelude.Bytes.bytesLE]
    congr 1
    · rw [← UInt8.ofNat_mod_size (x := v % _), Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
        UInt8.ofNat_mod_size]
    · rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm, show (2 : Nat) ^ 8 = 256 from rfl,
        Nat.mod_mul_right_div_self, ih]

private theorem chunked_toListFrom_succ (d : Prelude.Bytes.Chunked) (start n : Nat) :
    d.toListFrom start (n + 1) = d.getD start :: d.toListFrom (start + 1) n := by
  simp [Prelude.Bytes.Chunked.toListFrom, List.range'_succ]

private theorem chunked_toListFrom_add (d : Prelude.Bytes.Chunked) (start m n : Nat) :
    d.toListFrom start (m + n) = d.toListFrom start m ++ d.toListFrom (start + m) n := by
  have h := List.range'_append (s := start) (m := m) (n := n) (step := 1)
  rw [Nat.one_mul] at h
  simp only [Prelude.Bytes.Chunked.toListFrom, ← h, List.map_append]

/-- Bytes below `size` within chunk `c` are the chunk's, from their position in it. -/
private theorem chunked_toListFrom_chunk (d : Prelude.Bytes.Chunked) (c : Nat) {start count : Nat}
    (hlo : c * d.chunkSize ≤ d.base + start)
    (hhi : d.base + start + count ≤ (c + 1) * d.chunkSize) (hs : start + count ≤ d.size) :
    d.toListFrom start count =
      Prelude.Bytes.bytesLE count (d.chunk c >>> (8 * (d.base + start - c * d.chunkSize))) := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [chunked_toListFrom_succ, ih (by omega) (by omega) (by omega)]
    have hdiv : (d.base + start) / d.chunkSize = c := Nat.div_eq_of_lt_le hlo (by omega)
    have hmod : (d.base + start) % d.chunkSize = d.base + start - c * d.chunkSize := by
      rw [Nat.mod_eq_sub_mul_div, hdiv, Nat.mul_comm]
    have hchunk : d.chunks[c]! = d.chunk c := by
      simp [Prelude.Bytes.Chunked.chunk, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        List.getD_eq_getElem?_getD]
    have hlt : start < d.size := by omega
    simp only [Prelude.Bytes.bytesLE, Prelude.Bytes.Chunked.getD, Prelude.Bytes.Chunked.get?, hlt,
      ↓reduceIte, Option.getD_some, hdiv, hmod, hchunk]
    congr 2
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_add]
    congr 1
    omega

/-- `count` bytes from `start`, at most a chunk's size and below `size`, are `chunkedRead`'s. -/
theorem chunked_toListFrom_eq_read (d : Prelude.Bytes.Chunked) {start count : Nat}
    (hc : count ≤ d.chunkSize) (hs : start + count ≤ d.size) :
    d.toListFrom start count = chunkedRead d start count := by
  rcases Nat.eq_zero_or_pos d.chunkSize with h0 | hpos
  · obtain rfl : count = 0 := by omega
    rfl
  have hp := Nat.div_add_mod' (d.base + start) d.chunkSize
  have hk := Nat.mod_lt (d.base + start) hpos
  simp only [chunkedRead, bytesLE_mod]
  generalize (d.base + start) / d.chunkSize = c at *
  generalize (d.base + start) % d.chunkSize = k at *
  generalize hm : min count (d.chunkSize - k) = m
  obtain ⟨n, rfl⟩ : ∃ n, count = m + n := ⟨count - m, by omega⟩
  rw [chunked_toListFrom_add, Nat.add_sub_cancel_left,
    chunked_toListFrom_chunk d c (by omega) (by rw [Nat.succ_mul]; omega) (by omega),
    show d.base + start - c * d.chunkSize = k by omega]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  rw [chunked_toListFrom_chunk d (c + 1) (by rw [Nat.succ_mul]; omega)
    (by rw [Nat.succ_mul, Nat.succ_mul]; omega) (by omega),
    show d.base + (start + m) - (c + 1) * d.chunkSize = 0 by rw [Nat.succ_mul]; omega]
  rfl

/--
The code of a function or instruction inside an image: `n` bytes from offset `k` of one of its
sections are in memory at `sec.address + k`.
-/
theorem CodeIn.slice_of_section {sections : Prelude.ImageSections} {s : RamState}
    (h : CodeIn sections.toCodeMap s) {sec : Prelude.ImageSection} (hsec : sec ∈ sections)
    (k n : Nat) (hkn : k + n ≤ sec.bytes.size) :
    CodeIn (codeRange (sec.address + BitVec.ofNat 64 k) (sec.bytes.toListFrom k n)) s := by
  rw [← chunked_toList_slice _ _ _ hkn]
  refine h.mono fun x hx => ?_
  exact List.mem_flatMap.2 ⟨sec, hsec, codeRange_slice_subset _ _ k n x hx⟩

/-! ### The entry lemma -/

/-- Everything the library's triples assume of a program's starting state, for its code `code`. -/
structure EntryReady [Bindings] (code : CodeMap) (s : RamState) : Prop where
  /-- The machine facts every step lemma assumes. -/
  ready : ReadyToStep s
  /-- SSE enabled, for SSE triples. -/
  sse : Prelude.SupportedSSE Bindings.processor s
  /-- The program's code is in memory, below 4 GiB. -/
  code : CodeIn code s

/--
The entry lemma: a starting state stated with `Prelude`'s predicates, the decoder's LZCNT query
answered, and an image in memory below 4 GiB give `EntryReady`.
-/
theorem EntryReady.of_supported [instBindings : Bindings] {code : CodeMap} {s : RamState}
    (h : Prelude.SupportedIntegerMachineState Bindings.processor s)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hmt : Prelude.WriteBackMemoryType instBindings s 0)
    (hlzcnt : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding b)
    (hloaded : ∀ address byte, (address, byte) ∈ code → s.external[address]? = some byte)
    (hlow : CodeLow code) : EntryReady code s :=
  ⟨ReadyToStep.of_supported h hsmrr hmt (DecoderFeatures.of_supported h hlzcnt), h.sse,
    CodeIn.of_loaded hloaded hlow⟩

/-- `EntryReady.of_supported` for an image given as `Prelude.ImageSections`. -/
theorem EntryReady.of_sections [instBindings : Bindings] {sections : Prelude.ImageSections}
    {s : RamState}
    (h : Prelude.SupportedIntegerMachineState Bindings.processor s)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hmt : Prelude.WriteBackMemoryType instBindings s 0)
    (hlzcnt : ∃ b, Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding b)
    (hloaded : ∀ address byte, (address, byte) ∈ sections.toCodeMap →
      s.external[address]? = some byte)
    (hlow : SectionsLow sections) : EntryReady sections.toCodeMap s :=
  EntryReady.of_supported h hsmrr hmt hlzcnt hloaded hlow.codeLow

end X86Proofs
