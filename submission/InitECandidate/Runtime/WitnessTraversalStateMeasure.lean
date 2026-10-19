import InitECandidate.Runtime.DecodeWitnessTraversalMeasure
import InitECandidate.Runtime.WitnessTraversalChildCredit
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessTraversalTop {F : Type} (s : PanSemStateFiniteExact 64 F) : BitVec 64 :=
  match s.locals.lookup (ofString "top") with
  | some (.val (.word top)) => top
  | _ => 0

/-- Actual source modes are resolve2, decode1, and delivery0. -/
noncomputable def witnessTraversalModeCredit {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  by
  classical
  exact if s.locals.lookup (ofString "mode")=some (.val (.word (2 : BitVec 64))) then 3
  else if s.locals.lookup (ofString "mode")=some (.val (.word (1 : BitVec 64))) then 2 else 1

/-- A stopped loop has rank zero. Every running rank uses only actual source
locals, record memory and scratch globals, with no abstract counter oracle. -/
noncomputable def witnessTraversalStateMeasure {F : Type} (frame : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Nat :=
  by
  classical
  exact if s.locals.lookup (ofString "go")=some (.val (.word (0 : BitVec 64))) then 0 else
    decodeWitnessMeasure (decoderScratchCapacity frame s) (witnessTraversalTop s)
      (witnessTraversalChildCredit s (witnessTraversalTop s)) (witnessTraversalModeCredit s)

theorem witnessTraversalModeCredit_bound {F : Type} (s : PanSemStateFiniteExact 64 F) :
    witnessTraversalModeCredit s≤3 := by
  classical
  unfold witnessTraversalModeCredit
  split
  · omega
  · split <;> omega

theorem decoderScratchCapacity_bounded {F : Type} (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) :
    decoderScratchCapacity frame s≤(2^64-1)/88 := by
  classical
  unfold decoderScratchCapacity
  split
  · exact scratchRecordCapacity_bounded _ frame
  · omega

theorem witnessTraversalStateMeasure_bound {F : Type} (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) :
    witnessTraversalStateMeasure frame s < (((2^64-1)/88)+1)*decodeWitnessMeasureLayer := by
  classical
  have capacity := decoderScratchCapacity_bounded s frame
  have small := decodeWitnessMeasure_bound (decoderScratchCapacity frame s) (witnessTraversalTop s)
    (witnessTraversalChildCredit s (witnessTraversalTop s)) (witnessTraversalModeCredit s)
    (witnessTraversalChildCredit_bound s _) (witnessTraversalModeCredit_bound s)
  have ceiling := Nat.mul_le_mul_right decodeWitnessMeasureLayer (Nat.add_le_add_right capacity 1)
  unfold witnessTraversalStateMeasure
  split
  · unfold decodeWitnessMeasureLayer; omega
  · exact small.trans_le ceiling

theorem witnessTraversalStateMeasure_running {F : Type} (s : PanSemStateFiniteExact 64 F) (frame top : BitVec 64)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top))) :
    witnessTraversalStateMeasure frame s=decodeWitnessMeasure (decoderScratchCapacity frame s) top
      (witnessTraversalChildCredit s top) (witnessTraversalModeCredit s) := by
  classical
  have nonzero : s.locals.lookup (ofString "go")≠some (.val (.word (0 : BitVec 64))) := by
    rw [running]; simp
  simp only [witnessTraversalStateMeasure,if_neg nonzero,witnessTraversalTop,atTop]

theorem witnessTraversalModeCredit_delivery {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mode : s.locals.lookup (ofString "mode")=some (.val (.word (0#64)))) : witnessTraversalModeCredit s=1 := by
  classical
  change s.locals.lookup (ofString "mode")=some (.val (.word (0 : BitVec 64))) at mode
  simp [witnessTraversalModeCredit,mode]

theorem witnessTraversalModeCredit_decode {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mode : s.locals.lookup (ofString "mode")=some (.val (.word (1#64)))) : witnessTraversalModeCredit s=2 := by
  classical
  change s.locals.lookup (ofString "mode")=some (.val (.word (1 : BitVec 64))) at mode
  simp [witnessTraversalModeCredit,mode]

theorem witnessTraversalModeCredit_resolve {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mode : s.locals.lookup (ofString "mode")=some (.val (.word (2#64)))) : witnessTraversalModeCredit s=3 := by
  classical
  change s.locals.lookup (ofString "mode")=some (.val (.word (2 : BitVec 64))) at mode
  simp [witnessTraversalModeCredit,mode]

#print axioms witnessTraversalStateMeasure_bound
#print axioms witnessTraversalStateMeasure_running
#print axioms witnessTraversalModeCredit_delivery
#print axioms witnessTraversalModeCredit_decode
#print axioms witnessTraversalModeCredit_resolve
end InitECandidate.Runtime
