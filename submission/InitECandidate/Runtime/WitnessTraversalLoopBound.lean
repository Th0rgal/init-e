import InitECandidate.Runtime.WitnessTraversalIterationClosure
import InitECandidate.Runtime.WitnessTraversalRankFacts
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The exact original witness loop is bounded by its concrete natural rank.
All iteration costs, invariant preservation and strict descent come from the
actual source modes; rejection and other exceptional outcomes are included. -/
theorem witness_traversal_ranked_loop {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) (valid : WitnessTraversalRank layout s rank)
    (budget : rank*(witnessTraversalIterationCost layout.inputLimit+1)≤s.clock) :
    RankedOutcome s witnessTraversalCondition (rank*(witnessTraversalIterationCost layout.inputLimit+1))
      (fun {F} state n=>WitnessTraversalRank layout state n) False
      (evaluateHOLFiniteState s (.while witnessTraversalCondition decodeWitnessNodeIteration)) := by
  have installed : s.code=originalRuntimeCode := by
    obtain ⟨⟨scratch,heap,top,mode,go,state⟩,_⟩ := valid
    exact state.code
  apply rankedWhile_run witnessTraversalCondition decodeWitnessNodeIteration
    (witnessTraversalIterationCost layout.inputLimit) (fun {F} state n=>WitnessTraversalRank layout state n) False
    (fun state ranked word condition=>ranked.zero_exit layout state word condition) ?_ rank s installed valid budget
  intro G state n word code ranked condition nonzero ticks
  obtain ⟨⟨scratch,heap,top,mode,go,stateValid⟩,rankEq⟩ := ranked
  have running := stateValid.running_of_condition layout state scratch heap top mode go word condition nonzero
  have entryValid := stateValid.after_clock layout state scratch heap top mode go (state.clock-1)
  change WitnessTraversalState layout (decClockHOLFinite state) scratch heap top mode go at entryValid
  have entryTicks : witnessTraversalIterationCost layout.inputLimit≤(decClockHOLFinite state).clock := by
    change witnessTraversalIterationCost layout.inputLimit≤state.clock-1
    omega
  have bounded := entryValid.iteration_bound layout (decClockHOLFinite state) scratch heap top mode go entryTicks
  have control := witness_iteration_outcome_control (decClockHOLFinite state)
  have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) decodeWitnessNodeIteration
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
  · intro repeats
    have normal : (evaluateHOLFiniteState (decClockHOLFinite state) decodeWitnessNodeIteration).1=none := by
      rcases repeats with normal | continued
      · exact normal
      · exact False.elim (control.2 continued)
    let post := (evaluateHOLFiniteState (decClockHOLFinite state) decodeWitnessNodeIteration).2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) decodeWitnessNodeIteration=(none,post) :=
      Prod.ext normal rfl
    have kept := entryValid.iteration_preserves layout (decClockHOLFinite state) post scratch heap top mode go entryTicks run
    have decreased := entryValid.iteration_decreases layout (decClockHOLFinite state) post scratch heap top mode go running entryTicks run
    have oldMeasure : witnessTraversalStateMeasure layout.frame (decClockHOLFinite state)=
        witnessTraversalStateMeasure layout.frame state := rfl
    rw [oldMeasure,rankEq] at decreased
    exact ⟨witnessTraversalStateMeasure layout.frame post,by omega,⟨kept,rfl⟩,metadata.1⟩
  · intro broken
    exact False.elim (control.1 broken)

/-- A fixed finite rank ceiling depends only on the 64-bit address width. -/
def witnessTraversalRankCeiling : Nat := (((2^64-1)/88)+1)*decodeWitnessMeasureLayer

def witnessTraversalLoopCost (inputLimit : Nat) : Nat :=
  witnessTraversalRankCeiling*(witnessTraversalIterationCost inputLimit+1)

/-- Every actual invariant state has a uniform all-outcome loop bound. -/
theorem witness_traversal_loop_bounded {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalInvariant layout s)
    (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock) :
    RunBounded s (.while witnessTraversalCondition decodeWitnessNodeIteration) (witnessTraversalLoopCost layout.inputLimit) := by
  have ceiling := witnessTraversalStateMeasure_bound s layout.frame
  have costBound : witnessTraversalStateMeasure layout.frame s*(witnessTraversalIterationCost layout.inputLimit+1)≤
      witnessTraversalLoopCost layout.inputLimit :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt ceiling)
  have checked := witness_traversal_ranked_loop layout s (witnessTraversalStateMeasure layout.frame s)
    ⟨valid,rfl⟩ (costBound.trans budget)
  exact ⟨by have h:=checked.1;omega,checked.2.1,checked.2.2.1⟩

#print axioms witness_traversal_ranked_loop
#print axioms witness_traversal_loop_bounded
end InitECandidate.Runtime
