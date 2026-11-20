import X86Proofs.Step.Decode

/-!
# `Decode_Legacy_0`: dispatch on the opcode byte

The one place that looks inside `Decode_Legacy_0` (architecture rule 5). Without a REX2 prefix it
fetches the opcode byte at `ip`, checks a list of opcodes that are invalid in 64-bit mode
(`decodeLegacy0_modeGuard_run`), then dispatches on the byte to a per-opcode decoder
`Decode_Legacy_0_Opcode_XX`. `decodeLegacy0_run_of_opcodeXX` is that dispatch for one opcode byte:
if fetching the opcode at `ip` returns `XX` and leaves state `u` in 64-bit mode, the legacy decoder
runs the opcode-`XX` decoder from `u`.

The dispatch is a `match` on the byte, so a lemma names the byte; the proof is the same for every
byte (`decode_legacy0_dispatch`). Lemmas are given for the opcodes the library uses; for a new one,
add its one-liner here. The `+r` opcodes and `Jcc rel8` (one decoder per byte, all copies of the
first) have one lemma per range (`decodeLegacy0_run_of_opcode50to57`, `…58to5F`, `…91to97`,
`…B0toB7`, `…B8toBF`, `decodeLegacy0_run_of_jccOpcode8`). The `0F` map's dispatch,
`Decode_Legacy_1`, is `Step/Escape.lean`'s.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Proof of a `decodeLegacy0_run_of_opcodeXX` lemma: skip the REX2 branch, take the fetched opcode,
pass the invalid-opcode checks, and reduce the dispatch `match`. -/
local macro "decode_legacy0_dispatch" hrex2:term:max hfetch:term:max hmode:term:max : tactic =>
  `(tactic| (
    unfold Decode_Legacy_0
    rw [ite_eq_right (fun h => Bool.false_ne_true (($hrex2).symm.trans h))]
    rw [partialSpecM_liftTotal_bind_run _ _ $hfetch]
    repeat erw [decodeLegacy0_modeGuard_run _ _ $hmode]
    rfl))

section

variable [Bindings] (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
  (hrex2 : context.rex2_prefix_present = false)
include hrex2

/-- `Decode_Legacy_0` on opcode byte `00` (`ADD r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode00 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x00, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_00 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `01` (`ADD r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode01 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x01, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_01 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `02` (`ADD r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode02 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x02, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_02 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `03` (`ADD r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode03 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x03, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_03 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `04` (`ADD AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode04 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x04, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_04 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `05` (`ADD eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode05 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x05, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_05 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `08` (`OR r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode08 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x08, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_08 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `09` (`OR r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode09 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x09, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_09 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `0A` (`OR r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode0A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x0A, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_0A ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `0B` (`OR r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode0B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x0B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_0B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `0C` (`OR AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode0C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x0C, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_0C ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `0D` (`OR eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode0D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x0D, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_0D ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `10` (`ADC r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode10 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x10, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_10 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `11` (`ADC r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode11 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x11, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_11 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `12` (`ADC r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode12 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x12, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_12 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `13` (`ADC r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode13 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x13, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_13 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `14` (`ADC AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode14 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x14, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_14 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `15` (`ADC eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode15 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x15, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_15 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `18` (`SBB r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode18 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x18, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_18 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `19` (`SBB r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode19 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x19, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_19 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `1A` (`SBB r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode1A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1A, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_1A ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `1B` (`SBB r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode1B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_1B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `1C` (`SBB AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode1C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1C, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_1C ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `1D` (`SBB eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode1D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x1D, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_1D ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `20` (`AND r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode20 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x20, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_20 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `21` (`AND r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode21 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x21, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_21 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `22` (`AND r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode22 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x22, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_22 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `23` (`AND r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode23 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x23, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_23 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `24` (`AND AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode24 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x24, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_24 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `25` (`AND eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode25 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x25, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_25 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `28` (`SUB r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode28 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x28, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_28 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `29` (`SUB r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode29 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x29, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_29 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `2A` (`SUB r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode2A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2A, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_2A ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `2B` (`SUB r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode2B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_2B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `2C` (`SUB AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode2C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2C, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_2C ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `2D` (`SUB eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode2D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x2D, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_2D ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `30` (`XOR r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode30 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x30, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_30 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `31` (`XOR r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode31 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x31, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_31 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `32` (`XOR r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode32 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x32, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_32 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `33` (`XOR r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode33 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x33, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_33 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `34` (`XOR AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode34 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x34, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_34 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `35` (`XOR eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode35 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x35, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_35 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `38` (`CMP r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode38 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x38, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_38 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `39` (`CMP r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode39 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x39, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_39 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `3A` (`CMP r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode3A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x3A, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_3A ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `3B` (`CMP r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode3B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x3B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_3B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `3C` (`CMP AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode3C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x3C, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_3C ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `3D` (`CMP eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode3D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x3D, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_3D ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `63` (`MOVSXD r, r/m32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode63 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x63, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_63 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `68` (`PUSH imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode68 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x68, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_68 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `69` (`IMUL r, r/m, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode69 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x69, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_69 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `6A` (`PUSH imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode6A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6A, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_6A ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `6B` (`IMUL r, r/m, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode6B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x6B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_6B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `80` (group 1, `r/m8, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode80 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x80, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_80 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `81` (group 1, `r/m, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode81 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x81, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_81 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `83` (group 1, `r/m, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode83 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x83, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_83 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `84` (`TEST r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode84 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x84, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_84 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `85` (`TEST r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode85 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x85, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_85 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `86` (`XCHG r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode86 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x86, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_86 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `87` (`XCHG r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode87 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x87, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_87 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `88` (`MOV r/m8, r8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode88 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x88, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_88 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `89` (`MOV r/m, r`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode89 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x89, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_89 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `8A` (`MOV r8, r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode8A (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x8A, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_8A ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `8B` (`MOV r, r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode8B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x8B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_8B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `8C` (`MOV r/m, Sreg`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode8C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x8C, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_8C ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `8D` (`LEA`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode8D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x8D, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_8D ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `8F` (group 1A, `POP r/m64`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode8F (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x8F, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_8F ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `98` (`CBW`/`CWDE`/`CDQE`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode98 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x98, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_98 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `99` (`CWD`/`CDQ`/`CQO`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode99 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x99, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_99 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `9C` (`PUSHF`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode9C (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x9C, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_9C ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `9D` (`POPF`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode9D (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x9D, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_9D ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A0` (`MOV AL, moffs8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA0, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A0 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A1` (`MOV rAX, moffs`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA1, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A1 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A2` (`MOV moffs8, AL`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA2, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A2 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A3` (`MOV moffs, rAX`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA3, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A3 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A4` (`MOVSB`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA4 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA4, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A4 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A5` (`MOVSD`/`MOVSQ`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA5, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A5 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A8` (`TEST AL, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA8, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A8 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A9` (`TEST eAX, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA9, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A9 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A6` (`CMPSB`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA6, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A6 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `A7` (`CMPSW`/`CMPSD`/`CMPSQ`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeA7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xA7, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_A7 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `AA` (`STOSB`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeAA (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAA, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AA ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `AB` (`STOSW`/`STOSD`/`STOSQ`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeAB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAB, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AB ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `AC` (`LODSB`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeAC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAC, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AC ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `AD` (`LODSW`/`LODSD`/`LODSQ`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeAD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAD, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AD ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `AE` (`SCASB`) dispatches to its opcode decoder, which may
diverge (`PartialSpecM`: the `REPE`/`REPNE` forms loop). The dispatch arm is the decoder itself
rather than its `liftTotal`, so the last invalid-opcode check's mode read is run explicitly. -/
theorem decodeLegacy0_run_of_opcodeAE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAE, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_AE ip context).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `AF` (`SCASW`/`SCASD`/`SCASQ`) dispatches to its opcode decoder, which may
diverge (`PartialSpecM`: the `REPE`/`REPNE` forms loop). The dispatch arm is the decoder itself
rather than its `liftTotal`, so the last invalid-opcode check's mode read is run explicitly. -/
theorem decodeLegacy0_run_of_opcodeAF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAF, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_AF ip context).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `D8` (x87 arithmetic, `m32real` / ST(i)) dispatches to its
opcode decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeD8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD8, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_D8 ip context 0xD8).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `D9` (x87 loads, constants, control) dispatches to its opcode
decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeD9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD9, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_D9 ip context 0xD9).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `DA` (x87 `m32int`, FCMOVcc) dispatches to its opcode decoder,
which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeDA (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDA, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_DA ip context 0xDA).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `DB` (x87 `m32int`, `m80real`, FCMOVNcc, FCOMI) dispatches to
its opcode decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeDB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDB, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_DB ip context 0xDB).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `DC` (x87 arithmetic, `m64real` / ST(i)) dispatches to its
opcode decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeDC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDC, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_DC ip context 0xDC).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `DD` (x87 `m64real`, FST, FFREE) dispatches to its opcode
decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeDD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDD, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_DD ip context 0xDD).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `DE` (x87 `m16int`, popping arithmetic) dispatches to its
opcode decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeDE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDE, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_DE ip context 0xDE).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `DF` (x87 `m16int`, `m64int`, FCOMIP, FNSTSW AX) dispatches to
its opcode decoder, which may diverge (`PartialSpecM`) and takes the opcode byte (for FOP). -/
theorem decodeLegacy0_run_of_opcodeDF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xDF, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = (Decode_Legacy_0_Opcode_DF ip context 0xDF).run u := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true ((hrex2).symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  iterate 17 erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rw [partialSpecM_liftTotal_bind_run _ _ hmode]
  rfl

/-- `Decode_Legacy_0` on opcode byte `9B` (`FWAIT`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcode9B (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x9B, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_9B ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C0` (group 2, `r/m8, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC0, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C0 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C1` (group 2, `r/m, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC1, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C1 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C2` (`RET imm16`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC2, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C2 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C3` (`RET`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC3, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C3 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C6` (group 11, `r/m8, imm8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC6, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C6 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C7` (group 11, `r/m, imm32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC7, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C7 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C8` (`ENTER`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC8, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C8 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `C9` (`LEAVE`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeC9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xC9, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_C9 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `D0` (group 2, `r/m8, 1`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeD0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD0, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_D0 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `D1` (group 2, `r/m, 1`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeD1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD1, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_D1 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `D2` (group 2, `r/m8, CL`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeD2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD2, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_D2 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `D3` (group 2, `r/m, CL`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeD3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD3, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_D3 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `D7` (`XLAT`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeD7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xD7, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_D7 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `E0` (`LOOPNE rel8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeE0 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE0, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_E0 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `E1` (`LOOPE rel8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeE1 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE1, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_E1 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `E2` (`LOOP rel8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeE2 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE2, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_E2 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `E3` (`JRCXZ rel8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeE3 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE3, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_E3 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `E8` (`CALL rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeE8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE8, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_E8 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `E9` (`JMP rel32`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeE9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xE9, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_E9 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `EB` (`JMP rel8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeEB (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xEB, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_EB ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `F5` (`CMC`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeF5 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF5, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_F5 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `F6` (group 3, `r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeF6 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF6, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_F6 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `F7` (group 3, `r/m`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeF7 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF7, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_F7 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `F8` (`CLC`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeF8 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF8, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_F8 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `F9` (`STC`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeF9 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xF9, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_F9 ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `FC` (`CLD`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeFC (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFC, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_FC ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `FD` (`STD`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeFD (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFD, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_FD ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `FE` (group 4, `r/m8`) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeFE (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFE, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_FE ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `FF` (group 5) dispatches to its opcode decoder. -/
theorem decodeLegacy0_run_of_opcodeFF (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xFF, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_FF ip context).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- The `Jcc rel8` opcodes `70`–`7F`. -/
def jccOpcodes8 : List (BitVec 8) :=
  [0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F]

/-- `Decode_Legacy_0` on a `Jcc rel8` opcode (`70`–`7F`) dispatches to its decoder, a copy of the
`70` one (equal by `rfl`), with the opcode byte. -/
theorem decodeLegacy0_run_of_jccOpcode8 (op : BitVec 8) (hop : op ∈ jccOpcodes8)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_70 ip context op).run u) := by
  simp only [jccOpcodes8, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on opcode byte `90` (`NOP`, `PAUSE`) dispatches to its opcode decoder, with the
opcode byte. -/
theorem decodeLegacy0_run_of_opcode90 (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x90, u))
    (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_90 ip context 0x90).run u) := by
  decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on an opcode byte `50`–`57` (`PUSH r64`) dispatches to its opcode decoder, a
copy of the `50` one (equal by `rfl`), with the opcode byte. -/
theorem decodeLegacy0_run_of_opcode50to57 (op : UInt8)
    (hop : op ∈ [0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57])
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_50 ip context op.toBitVec).run u) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on an opcode byte `58`–`5F` (`POP r64`) dispatches to its opcode decoder, a
copy of the `58` one (equal by `rfl`), with the opcode byte. -/
theorem decodeLegacy0_run_of_opcode58to5F (op : UInt8)
    (hop : op ∈ [0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F])
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_58 ip context op.toBitVec).run u) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on an opcode byte `91`–`97` (`XCHG r, rAX`) dispatches to its opcode decoder,
a copy of the `91` one (equal by `rfl`), with the opcode byte. -/
theorem decodeLegacy0_run_of_opcode91to97 (op : UInt8)
    (hop : op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_91 ip context op.toBitVec).run u) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on an opcode byte `B0`–`B7` (`MOV r8, imm8`) dispatches to its opcode
decoder, a copy of the `B0` one (equal by `rfl`), with the opcode byte. -/
theorem decodeLegacy0_run_of_opcodeB0toB7 (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7])
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_B0 ip context op.toBitVec).run u) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decode_legacy0_dispatch hrex2 hfetch hmode

/-- `Decode_Legacy_0` on an opcode byte `B8`–`BF` (`MOV r, imm`) dispatches to its opcode decoder, a
copy of the `B8` one (equal by `rfl`), with the opcode byte. -/
theorem decodeLegacy0_run_of_opcodeB8toBF (op : UInt8)
    (hop : op ∈ [0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF])
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_B8 ip context op.toBitVec).run u) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decode_legacy0_dispatch hrex2 hfetch hmode

end

end X86Proofs
