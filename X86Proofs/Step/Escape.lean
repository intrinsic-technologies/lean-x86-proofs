import X86Proofs.Step.PrefixScan

/-!
# The `0F` map: `Decode_Legacy_1` dispatch

After the `0F` escape the prefix scan runs `Decode_Legacy_1` at the second opcode byte
(`fetchAndExecute_scan_legacy1_of_fetchReady`, `step_scan_legacy1`). Like `Decode_Legacy_0` it
fetches that byte again, checks a list of opcodes that are invalid in 64-bit mode, then dispatches
on the byte to a per-opcode decoder `Decode_Legacy_1_Opcode_XX`. `decodeLegacy1_run_of_opcodeXX` is
that dispatch for one second byte, the analogue of `decodeLegacy0_run_of_opcodeXX`
(`Step/Decode/Legacy0.lean`); each 0F form's decode lemma is then this plus its opcode decoder, as
for one-byte opcodes.

The dispatch is a `match` on the byte, so a lemma names the byte; the proof is the same for every
byte (`decode_legacy1_dispatch`; `decode_legacy1_dispatch_partial` for the decoders that may
diverge, whose dispatch arm is not a `liftTotal`). Five of the invalid-opcode checks also test the
`66` and REP prefixes (`decodeLegacy1_modeGuard_run`). Lemmas are given for the second bytes the
library uses: `00` (sldt, str), `01` (smsw), `10`, `11` (movups/pd, movss), `12`, `13` (movlps/pd,
movhlps), `16`, `17` (movhps/pd, movlhps), `14`, `15` (unpcklps/pd, unpckhps/pd), `18`–`1D` (the
reserved hint NOPs), `1E` (endbr64, a reserved NOP), `1F` (nop), `28`, `29` (movaps/pd), `6F`, `7F`
(movdqa, movdqu), `D6` (movq), `50` (movmskps/pd), `54`–`57` (andps, andnps, orps, xorps and their
`pd` forms), `51`, `58`, `59`, `5C`–`5F` (the floating-point sqrt, add, mul, sub, min, div, max in
their `ps`, `pd`, `ss`, `sd` forms), `2E`, `2F` (ucomiss/sd, comiss/sd), `C2` (cmpps/pd/ss/sd),
`5A`, `5B`, `E6` (the float conversions cvtps2pd, cvtpd2ps, cvtss2sd, cvtsd2ss, cvtdq2ps, cvtdq2pd,
cvtps2dq, cvttps2dq, cvtpd2dq, cvttpd2dq; `5B` and `E6` may diverge: `PartialSpecM`), `2A`
(cvtsi2ss, cvtsi2sd), `2C`, `2D` (cvttss2si, cvttsd2si, cvtss2si, cvtsd2si; these may diverge),
`52`, `53` (rsqrtps/ss, rcpps/ss), `AE` (ldmxcsr, stmxcsr), `2B` (movntps/pd), `E7` (movntdq), `C3`
(movnti), `F7` (maskmovdqu, maskmovq), `77` (emms), the SSE2 packed-integer opcodes `60`–`6D`,
`74`–`76`, `D1`–`D5`, `D8`–`E5`, `E8`–`EF`, `F1`–`F6`, `F8`–`FE` (`sse_bin`), `D7` (pmovmskb), `6E`,
`7E` (movd/movq with a general-purpose register or memory; movq `F3 0F 7E`), `71`–`73` (shifts by an
immediate), `70` (pshufd, pshufhw), `C4` (pinsrw), `C5` (pextrw), `C6` (shufps/pd) (these four may
diverge: `PartialSpecM`), `82`–`87` and `80`–`8F` together (`decodeLegacy1_run_of_jccOpcode32`; Jcc
rel32), `40`–`4F` together (`decodeLegacy1_run_of_cmovOpcode`; CMOVcc), `90`–`9F` together
(`decodeLegacy1_run_of_setccOpcode`; SETcc), `C8`–`CF` together (`decodeLegacy1_run_of_bswapOpcode`;
BSWAP), `A0`, `A8` (push fs, push gs), `A2` (cpuid), `A3`, `AB`, `B3`, `BA`, `BB` (bit test), `A4`,
`A5`, `AC`, `AD` (shld, shrd), `AF` (imul), `B0`, `B1` (cmpxchg), `B6`, `B7` (movzx), `BE`, `BF`
(movsx), `BC`, `BD` (bit scan), `C0`, `C1` (xadd), `C7` (cmpxchg8b). This is the one place that
looks inside `Decode_Legacy_1` (architecture rule 5).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
One of `Decode_Legacy_1`'s invalid-opcode checks that also tests the `66` and REP prefixes
(`opcode == n and not osz and rep == 0`), once the opcode is known not to be `n`: in 64-bit
mode it passes whatever the prefixes.
-/
theorem decodeLegacy1_modeGuard_run [Bindings] (s : RamState) (a b : Bool)
    (next : Unit → X86.Runtime.PartialSpecM X86.Exception RamState Unit) (hmode : In64BitMode s) :
    (do
      let mode ← X86.Runtime.liftTotal In_64Bit_Mode
      if strictAnd (strictAnd (strictAnd mode false) a) b then
        let result : Unit ← liftM Report_Invalid_Opcode
        next result
      else
        next ()).run s = (next ()).run s := by
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- Proof of a `decode_legacy1_XX` lemma: skip the REX2 branch, take the fetched opcode, pass the
invalid-opcode checks, and reduce the dispatch `match`. -/
local macro "decode_legacy1_dispatch" hrex2:term:max hfetch:term:max hmode:term:max : tactic => `(tactic| (
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (($hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ $hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ $hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ $hmode]
  rfl))

/-- `decode_legacy1_dispatch` for a byte whose opcode decoder may diverge (`PartialSpecM`: `70`,
`C4`, `C5`, `C6`): the dispatch arm is the decoder itself rather than its `liftTotal`, so the four
prefix-testing checks are passed one by one and the last check's mode read is run explicitly. -/
local macro "decode_legacy1_dispatch_partial" hrex2:term:max hfetch:term:max hmode:term:max :
    tactic => `(tactic| (
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (($hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ $hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ $hmode]
  iterate 4 erw [decodeLegacy1_modeGuard_run _ _ _ _ $hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ $hmode]
  rfl))

section

variable [Bindings] (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
  (hrex2 : context.rex2_prefix_present = false) (hmode : In64BitMode u)
include hrex2 hmode

/-- `Decode_Legacy_1` on second byte `00` (group 6: SLDT, STR, …) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode00 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x00, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_00 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `01` (group 7: SMSW, SGDT, …) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode01 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x01, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_01 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `10` (`movups`, …) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode10 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x10, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_10 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `11` (`movups`, `movupd`, `movss` stores) dispatches to its
opcode decoder. -/
theorem decodeLegacy1_run_of_opcode11 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x11, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_11 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `12` (`movlps`, `movlpd`, `movhlps`) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode12 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x12, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_12 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `13` (`movlps`, `movlpd` stores) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode13 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x13, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_13 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `14` (`unpcklps`, `unpcklpd`) dispatches to its opcode decoder.
-/
theorem decodeLegacy1_run_of_opcode14 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x14, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_14 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `15` (`unpckhps`, `unpckhpd`) dispatches to its opcode decoder.
-/
theorem decodeLegacy1_run_of_opcode15 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x15, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_15 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `16` (`movhps`, `movhpd`, `movlhps`) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode16 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x16, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_16 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `17` (`movhps`, `movhpd` stores) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode17 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x17, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_17 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `18` (prefetches, reserved NOPs) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode18 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x18, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_18 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `19` (reserved NOPs) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode19 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x19, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_19 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `1A` (reserved NOPs) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode1A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1A, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_1A ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `1B` (reserved NOPs) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode1B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1B, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_1B ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `1C` (reserved NOPs) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode1C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1C, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_1C ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `1D` (reserved NOPs) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode1D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1D, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_1D ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `1E` (endbr64 and reserved NOPs) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode1E (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1E, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_1E ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `1F` (`nop r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode1F (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1F, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_1F ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `28` (`movaps`, `movapd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode28 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x28, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_28 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `29` (`movaps m, xmm`, …) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode29 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x29, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_29 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `2B` (`movntps`, `movntpd`) dispatches to its opcode decoder.
-/
theorem decodeLegacy1_run_of_opcode2B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2B, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_2B ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `50` (`movmskps`, `movmskpd`) dispatches to its opcode decoder.
-/
theorem decodeLegacy1_run_of_opcode50 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x50, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_50 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `54` (`andps`, `andpd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode54 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x54, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_54 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `55` (`andnps`, `andnpd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode55 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x55, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_55 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `56` (`orps`, `orpd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode56 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x56, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_56 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `57` (`xorps`, …) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode57 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x57, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_57 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `51` (`sqrtps`, `sqrtpd`, `sqrtss`, `sqrtsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode51 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x51, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_51 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `58` (`addps`, `addpd`, `addss`, `addsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode58 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x58, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_58 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `59` (`mulps`, `mulpd`, `mulss`, `mulsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode59 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x59, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_59 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `5C` (`subps`, `subpd`, `subss`, `subsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode5C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x5C, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_5C ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `5D` (`minps`, `minpd`, `minss`, `minsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode5D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x5D, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_5D ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `5E` (`divps`, `divpd`, `divss`, `divsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode5E (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x5E, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_5E ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `5F` (`maxps`, `maxpd`, `maxss`, `maxsd`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode5F (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x5F, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_5F ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C2` (`cmpps`, `cmppd`, `cmpss`, `cmpsd`) dispatches to its
opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeC2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC2, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_C2 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `5A` (`cvtps2pd`, `cvtpd2ps`, `cvtss2sd`, `cvtsd2ss`)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode5A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x5A, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_5A ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `5B` (`cvtdq2ps`, `cvtps2dq`, `cvttps2dq`) dispatches to its
opcode decoder, which may diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcode5B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x5B, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_5B ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E6` (`cvtdq2pd`, `cvttpd2dq`, `cvtpd2dq`) dispatches to its
opcode decoder, which may diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcodeE6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE6, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_E6 ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `2A` (`cvtsi2ss`, `cvtsi2sd`, …) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode2A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2A, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_2A ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `2C` (`cvttss2si`, `cvttsd2si`, …) dispatches to its opcode
decoder, which may diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcode2C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2C, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_2C ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `2D` (`cvtss2si`, `cvtsd2si`, …) dispatches to its opcode
decoder, which may diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcode2D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2D, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_2D ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `52` (`rsqrtps`, `rsqrtss`) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode52 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x52, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_52 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `53` (`rcpps`, `rcpss`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode53 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x53, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_53 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `2E` (`ucomiss`, `ucomisd`) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode2E (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2E, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_2E ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `2F` (`comiss`, `comisd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode2F (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2F, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_2F ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `AE` (group 15: `ldmxcsr`, `stmxcsr`, …) dispatches to its
opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeAE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAE, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_AE ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `60` (`punpcklbw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode60 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x60, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_60 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `61` (`punpcklwd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode61 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x61, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_61 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `62` (`punpckldq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode62 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x62, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_62 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `63` (`packsswb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode63 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x63, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_63 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `64` (`pcmpgtb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode64 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x64, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_64 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `65` (`pcmpgtw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode65 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x65, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_65 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `66` (`pcmpgtd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode66 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x66, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_66 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `67` (`packuswb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode67 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x67, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_67 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `68` (`punpckhbw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode68 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x68, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_68 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `69` (`punpckhwd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode69 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x69, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_69 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `6A` (`punpckhdq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode6A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6A, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_6A ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `6B` (`packssdw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode6B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6B, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_6B ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `6C` (`punpcklqdq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode6C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6C, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_6C ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `6D` (`punpckhqdq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode6D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6D, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_6D ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `6F` (`movdqa`, `movdqu`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode6F (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6F, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_6F ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `70` (`pshufd`, `pshuflw`, `pshufhw`) dispatches to its opcode
decoder, which may diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcode70 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x70, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_70 ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `71` (group 12: `psrlw`, `psraw`, `psllw` by an immediate)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode71 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x71, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_71 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `72` (group 13: `psrld`, `psrad`, `pslld` by an immediate)
dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode72 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x72, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_72 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `73` (group 14: `psrlq`, `psrldq`, `psllq`, `pslldq` by an
immediate) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode73 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x73, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_73 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `6E` (`movd`/`movq xmm, r/m`) dispatches to its opcode decoder.
-/
theorem decodeLegacy1_run_of_opcode6E (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6E, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_6E ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `74` (`pcmpeqb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode74 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x74, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_74 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `75` (`pcmpeqw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode75 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x75, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_75 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `76` (`pcmpeqd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode76 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x76, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_76 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `7E` (`movd`/`movq r/m, xmm`) dispatches to its opcode decoder.
-/
theorem decodeLegacy1_run_of_opcode7E (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x7E, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_7E ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `7F` (`movdqa`, `movdqu` stores) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcode7F (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x7F, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_7F ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C3` (`movnti`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeC3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC3, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_C3 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E7` (`movntdq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE7, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E7 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F7` (`maskmovdqu`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF7, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F7 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `77` (`emms`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode77 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x77, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_77 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `A0` (`push fs`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeA0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA0, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A0 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `A8` (`push gs`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeA8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA8, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A8 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `A2` (`CPUID`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeA2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA2, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A2 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `A3` (`BT r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeA3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA3, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A3 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `A4` (`SHLD r/m, r, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeA4 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA4, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A4 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `A5` (`SHLD r/m, r, CL`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeA5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA5, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A5 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `AB` (`BTS r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeAB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAB, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_AB ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `AC` (`SHRD r/m, r, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeAC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAC, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_AC ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `AD` (`SHRD r/m, r, CL`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeAD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAD, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_AD ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `AF` (`IMUL r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeAF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAF, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_AF ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `B0` (`cmpxchg r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeB0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xB0, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_B0 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `B1` (`cmpxchg r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeB1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xB1, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_B1 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `B3` (`BTR r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeB3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xB3, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_B3 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `B6` (`movzx r, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeB6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xB6, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_B6 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `B7` (`movzx r, r/m16`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeB7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xB7, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_B7 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `BA` (group 8: `BT`, `BTS`, `BTR`, `BTC r/m, imm8`) dispatches
to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeBA (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBA, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_BA ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `BB` (`BTC r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeBB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBB, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_BB ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `BC` (`BSF r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeBC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBC, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_BC ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `BD` (`BSR r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeBD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBD, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_BD ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `BE` (`movsx r, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeBE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBE, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_BE ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `BF` (`movsx r, r/m16`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeBF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBF, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_BF ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C0` (`xadd r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeC0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC0, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_C0 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C1` (`xadd r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeC1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC1, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_C1 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C4` (`pinsrw`) dispatches to its opcode decoder, which may
diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcodeC4 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC4, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_C4 ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C5` (`pextrw`) dispatches to its opcode decoder, which may
diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcodeC5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC5, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_C5 ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C6` (`shufps`, `shufpd`) dispatches to its opcode decoder,
which may diverge (`PartialSpecM`). -/
theorem decodeLegacy1_run_of_opcodeC6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC6, u)) :
    (Decode_Legacy_1 ip context).run s = (Decode_Legacy_1_Opcode_C6 ip context).run u := by
  decode_legacy1_dispatch_partial hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `C7` (group 9: `cmpxchg8b m64`) dispatches to its opcode
decoder. -/
theorem decodeLegacy1_run_of_opcodeC7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC7, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_C7 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D1` (`psrlw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD1, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D1 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D2` (`psrld`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD2, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D2 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D3` (`psrlq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD3, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D3 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D4` (`paddq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD4 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD4, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D4 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D5` (`pmullw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD5, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D5 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D6` (`movq xmm/m64, xmm`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD6, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D6 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D7` (`pmovmskb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD7, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D7 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D8` (`psubusb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD8, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D8 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `D9` (`psubusw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeD9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD9, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_D9 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `DA` (`pminub`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeDA (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDA, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_DA ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `DB` (`pand`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeDB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDB, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_DB ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `DC` (`paddusb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeDC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDC, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_DC ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `DD` (`paddusw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeDD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDD, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_DD ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `DE` (`pmaxub`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeDE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDE, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_DE ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `DF` (`pandn`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeDF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDF, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_DF ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E0` (`pavgb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE0, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E0 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E1` (`psraw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE1, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E1 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E2` (`psrad`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE2, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E2 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E3` (`pavgw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE3, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E3 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E4` (`pmulhuw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE4 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE4, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E4 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E5` (`pmulhw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE5, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E5 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E8` (`psubsb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE8, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E8 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `E9` (`psubsw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeE9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE9, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_E9 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `EA` (`pminsw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeEA (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xEA, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_EA ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `EB` (`por`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeEB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xEB, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_EB ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `EC` (`paddsb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeEC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xEC, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_EC ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `ED` (`paddsw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeED (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xED, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_ED ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `EE` (`pmaxsw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeEE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xEE, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_EE ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `EF` (`pxor`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeEF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xEF, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_EF ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F1` (`psllw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF1, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F1 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F2` (`pslld`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF2, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F2 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F3` (`psllq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF3, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F3 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F4` (`pmuludq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF4 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF4, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F4 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F5` (`pmaddwd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF5, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F5 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F6` (`psadbw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF6, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F6 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F8` (`psubb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF8, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F8 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `F9` (`psubw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeF9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF9, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_F9 ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `FA` (`psubd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeFA (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFA, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_FA ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `FB` (`psubq`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeFB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFB, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_FB ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `FC` (`paddb`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeFC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFC, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_FC ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `FD` (`paddw`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeFD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFD, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_FD ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `FE` (`paddd`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcodeFE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFE, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_FE ip context).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `82` (`jb rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode82 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x82, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_82 ip context 0x82).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `83` (`jae rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode83 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x83, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_83 ip context 0x83).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `84` (`je rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode84 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x84, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_84 ip context 0x84).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `85` (`jne rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode85 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x85, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_85 ip context 0x85).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `86` (`jbe rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode86 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x86, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_86 ip context 0x86).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_1` on second byte `87` (`ja rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy1_run_of_opcode87 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x87, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_87 ip context 0x87).run u) := by
  decode_legacy1_dispatch hrex2 hfetch hmode

/-- The second bytes `80`–`8F` of the `Jcc rel32` opcodes `0F 80`–`0F 8F`. -/
def jccOpcodes32 : List (BitVec 8) :=
  [0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F]

/-- `Decode_Legacy_1` on a `Jcc rel32` second byte (`80`–`8F`) dispatches to its decoder, a copy of
the `80` one (equal by `rfl`), with the byte. -/
theorem decodeLegacy1_run_of_jccOpcode32 (op : BitVec 8) (hop : op ∈ jccOpcodes32)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_80 ip context op).run u) := by
  simp only [jccOpcodes32, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    decode_legacy1_dispatch hrex2 hfetch hmode

/-- The second bytes `40`–`4F` of the `CMOVcc` opcodes `0F 40`–`0F 4F`. -/
def cmovOpcodes : List (BitVec 8) :=
  [0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F]

/-- `Decode_Legacy_1` on a `CMOVcc` second byte (`40`–`4F`) dispatches to its decoder, a copy of
the `40` one (equal by `rfl`), with the byte. -/
theorem decodeLegacy1_run_of_cmovOpcode (op : BitVec 8) (hop : op ∈ cmovOpcodes)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_40 ip context op).run u) := by
  simp only [cmovOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    decode_legacy1_dispatch hrex2 hfetch hmode

/-- The second bytes `90`–`9F` of the `SETcc` opcodes `0F 90`–`0F 9F`. -/
def setccOpcodes : List (BitVec 8) :=
  [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F]

/-- `Decode_Legacy_1` on a `SETcc` second byte (`90`–`9F`) dispatches to its decoder, a copy of
the `90` one (equal by `rfl`), with the byte. -/
theorem decodeLegacy1_run_of_setccOpcode (op : BitVec 8) (hop : op ∈ setccOpcodes)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_90 ip context op).run u) := by
  simp only [setccOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    decode_legacy1_dispatch hrex2 hfetch hmode

/-- The second bytes `C8`–`CF` of the `BSWAP` opcodes `0F C8+r`. -/
def bswapOpcodes : List (BitVec 8) := [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]

/-- `Decode_Legacy_1` on a `BSWAP` second byte (`C8`–`CF`) dispatches to its decoder, a copy of
the `C8` one (equal by `rfl`), with the byte. -/
theorem decodeLegacy1_run_of_bswapOpcode (op : BitVec 8) (hop : op ∈ bswapOpcodes)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_C8 ip context op).run u) := by
  simp only [bswapOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decode_legacy1_dispatch hrex2 hfetch hmode

end

/-- The second byte of the `CMOVcc` opcode for condition `cc`: `0F (40 + cc)`. -/
def cmovOpcode (cc : BitVec 4) : UInt8 := UInt8.ofNat (0x40 + cc.toNat)

/-- The second byte of the `SETcc` opcode for condition `cc`: `0F (90 + cc)`. -/
def setccOpcode (cc : BitVec 4) : UInt8 := UInt8.ofNat (0x90 + cc.toNat)

theorem cmovOpcode_mem (cc : BitVec 4) : (cmovOpcode cc).toBitVec ∈ cmovOpcodes := by
  revert cc
  decide

theorem setccOpcode_mem (cc : BitVec 4) : (setccOpcode cc).toBitVec ∈ setccOpcodes := by
  revert cc
  decide

/-- The condition a `CMOVcc` form reads from its opcode byte (the low four bits) is `cc`. -/
theorem cmovOpcode_cc (cc : BitVec 4) : (cmovOpcode cc).toBitVec.extractLsb' 0 4 = cc := by
  revert cc
  decide

/-- The condition a `SETcc` form reads from its opcode byte (the low four bits) is `cc`. -/
theorem setccOpcode_cc (cc : BitVec 4) : (setccOpcode cc).toBitVec.extractLsb' 0 4 = cc := by
  revert cc
  decide

/-- A `CMOVcc` second byte is not a three-byte escape (`38`, `3A`). -/
theorem cmovOpcode_ne (cc : BitVec 4) : cmovOpcode cc ≠ 0x38 ∧ cmovOpcode cc ≠ 0x3A := by
  revert cc
  decide

/-- A `SETcc` second byte is not a three-byte escape (`38`, `3A`). -/
theorem setccOpcode_ne (cc : BitVec 4) : setccOpcode cc ≠ 0x38 ∧ setccOpcode cc ≠ 0x3A := by
  revert cc
  decide

/-- A long multi-byte NOP, `66 66 66 66 2E 0F 1F …`: the scan reaches `Decode_Legacy_1` at RIP + 6
after 7 fetches, with operand size 16; the `2E` prefix leaves the segment alone in 64-bit mode. -/
example [Bindings] (s : RamState) (h : ReadyToStep s) (rest : List UInt8)
    (hcode : BytesAt s s.RIP ([0x66, 0x66, 0x66, 0x66, 0x2E] ++ 0x0F :: 0x1F :: rest))
    (hlow : s.RIP.toNat + ([0x66, 0x66, 0x66, 0x66, 0x2E] ++ 0x0F :: 0x1F :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded false
        (Decode_Legacy_1 (BitVec.add s.RIP 6#64) (oszContext s.DS))).run
        (afterFetches (beforeFetch s) 7) := by
  rw [fetchAndExecute_scan_legacy1 s h _ 0x1F rest (scanPrefix_of_66_2e (by decide)) (by decide)
    (by decide) hcode hlow, scanContext_66x4_2e]
  rfl

end X86Proofs
