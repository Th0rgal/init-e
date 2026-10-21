import ActualCandidateHeaderStore
import InitECandidate.Runtime.GuestCostChargeFamily

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- Costed run of a header address `t + offset`. -/
theorem candidate_header_address_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tbase : BitVec 64) (offset : Nat)
    (tLocal : s.locals.lookup (ofString "t") = some (.val (.word tbase))) :
    CostedExpressionRun s
      (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 offset)])
      (some (.val (.word (tbase + BitVec.ofNat 64 offset))))
      (expressionEvents s
        (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 offset)])) := by
  apply costedExpression_events
  simp [expressionValue, evalHOLExact, evalListHOLExact, tLocal, valueIsWord, wordOpHOL,
    wordOp, valueWord]

/-- Costed run of a word-valued local. -/
theorem candidate_header_local_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : BitVec 64)
    (localEq : s.locals.lookup name = some (.val (.word value))) :
    CostedExpressionRun s (.var .local name) (some (.val (.word value)))
      (expressionEvents s (.var .local name)) := by
  apply costedExpression_events
  simp [expressionValue, evalHOLExact, evalListHOLExact, localEq, valueIsWord]

/-- Costed run of a constant word. -/
theorem candidate_header_const_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (value : BitVec 64) :
    CostedExpressionRun s (.const value) (some (.val (.word value)))
      (expressionEvents s (.const value)) := by
  apply costedExpression_events
  simp [expressionValue, evalHOLExact, evalListHOLExact, valueIsWord]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_header_address_run
#print axioms BoundedTableExperiment.candidate_header_local_run
#print axioms BoundedTableExperiment.candidate_header_const_run
