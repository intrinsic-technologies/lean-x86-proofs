import X86Proofs.Core.Float

/-!
# CVTPD2PS specification

`CVTPD2PS xmm1, xmm2/m128` (`66 0F 5A /r`) converts the two double-precision elements of the
source to single precision: `DEST[32i+31:32i] ← Convert(SRC[64i+63:64i])` for `i` = 0, 1,
`DEST[127:64]` zero, rounded as MXCSR.RC says, with MXCSR's DAZ and FTZ; the exception flags of
both lanes are ORed into MXCSR. Each lane and its flags are lean-x86's own `FP.Convert` at that
MXCSR (`fpConvert`, `Core/Float.lean`); there is no IEEE-754 library to state them against
independently. `cvtpd2psSpec mx a b` is the result (the destination `a` is not read),
`cvtpd2psFlags mx a b` the exception flags, `cvtpd2psOk mx a b` that lean-x86 returns both lanes;
lean-x86 computes them with `Operations.CVTPg2Pf 64 128 32 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags (MXCSR's rounding control and FTZ). -/
def cvtpd2psLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  fpConvert 64 32 (rcMode (mxRc mx)) (mxFtz mx) mx (lane 64 b i)

/-- The two double-precision lanes of `b` converted to single precision at MXCSR `mx`, in the two
low lanes of zero. -/
def cvtpd2psSpec (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpLanes 2 32 (cvtpd2psLane mx b)

/-- The exception flags, both lanes' ORed. -/
def cvtpd2psFlags (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpLanesFlags 2 32 (cvtpd2psLane mx b)

/-- lean-x86's conversion returns a value on both lanes (`FpConvertOk`). -/
def cvtpd2psOk (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 2, FpConvertOk 64 32 (rcMode (mxRc mx)) (mxFtz mx) mx (lane 64 b i)

theorem cvtpd2ps_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvtpd2psOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTPg2Pf 64 128 32 128 b ctx mod).run s =
      (.ok (cvtpd2psSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtpd2psFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTPg2Pf
  fp_packed_start_sqrt hb
  fp_cvt_loop 2 64 128 32 (fun i hi => fpConvert_run 64 32 (.inr ⟨rfl, rfl⟩) _ _ _ _ (hok i hi)) hm

end X86Proofs
