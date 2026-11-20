import X86Proofs.Core.Float
import X86.Instructions.CVTPI2PS

/-!
# CVTPI2PS specification

`CVTPI2PS xmm, mm` (`NP 0F 2A /r`, `mod = 3`) converts the two signed doubleword integers of the
MMX register to single precision: `DEST[31:0] ← Convert(SRC[31:0])`, `DEST[63:32] ←
Convert(SRC[63:32])`, rounded as MXCSR.RC says; the upper two lanes of the destination are kept.
The exception flags (precision only, after `FP.Prioritize_Operand_Exceptions`) of both lanes are
ORed into MXCSR. Each lane and its flags are lean-x86's own `FP.From_Int` at that MXCSR
(`fpFromInt`, `Core/Float.lean`). `cvtpi2psSpec mx a b` is the result (`a` the destination's old
value), `cvtpi2psFlags mx a b` the exception flags, `cvtpi2psOk mx a b` that lean-x86 returns both
lanes; lean-x86 computes them with `Operations.CVTPI2PS`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags. -/
def cvtpi2psLane (mx : BitVec 32) (b : BitVec 64) (i : Nat) : BitVec 32 × BitVec 6 :=
  ((fpFromInt 32 32 mx (lane 32 b i)).1, fpOperandPrio (fpFromInt 32 32 mx (lane 32 b i)).2)

/-- The two doubleword lanes of `b` converted to single precision at MXCSR `mx`, in the two low
lanes of `a`. -/
def cvtpi2psSpec (mx : BitVec 32) (a : BitVec 128) (b : BitVec 64) : BitVec 128 :=
  (fpLanesOnto 2 32 (cvtpi2psLane mx b) a).2

/-- The exception flags, both lanes' ORed. -/
def cvtpi2psFlags (mx : BitVec 32) (a : BitVec 128) (b : BitVec 64) : BitVec 6 :=
  (fpLanesOnto 2 32 (cvtpi2psLane mx b) a).1

/-- lean-x86's conversion returns a value on both lanes (`FpFromIntOk`). -/
def cvtpi2psOk (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 64) : Prop :=
  ∀ i < 2, FpFromIntOk 32 32 mx (lane 32 b i)

theorem cvtpi2ps_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a : BitVec 128)
    (b : BitVec 64) (hm : MxcsrPre s) (hok : cvtpi2psOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTPI2PS a b).run s =
      (.ok (cvtpi2psSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtpi2psFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTPI2PS
  simp (config := { decide := true }) only [x86_runtime, pure_bind]
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  fp_cvt_loop 2 32 64 32 (fun i hi => fpFromInt_run 32 32 (.inl rfl) (.inl rfl) _ _ (hok i hi))
    hm masked

end X86Proofs
