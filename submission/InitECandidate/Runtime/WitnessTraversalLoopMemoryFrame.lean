import InitECandidate.Runtime.WitnessTraversalLoopBound
import InitECandidate.Runtime.WitnessTraversalIterationMemoryFrame
import InitECandidate.Runtime.WitnessTraversalIterationClosure
import InitECandidate.Runtime.WitnessTraversalRankFacts
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The exact original witness loop is bounded by its concrete natural rank.
All iteration costs, invariant preservation and strict descent come from the
actual source modes; rejection and other exceptional outcomes are included. -/
theorem witness_traversal_ranked_loop_memory {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (watched : BitVec 64) (word : HolWordLab 64)
    (above : layout.databaseCeiling≤watched.toNat) (below : watched.toNat<layout.dbHeap.toNat)
    (rank : Nat) (valid : WitnessTraversalRank layout s rank) (atWord : s.memory watched=word)
    (budget : rank*(witnessTraversalIterationCost layout.inputLimit+1)≤s.clock) :
    RankedOutcome s witnessTraversalCondition (rank*(witnessTraversalIterationCost layout.inputLimit+1))
      (fun {F} state n=>WitnessTraversalRank layout state n ∧state.memory watched=word) False
      (evaluateHOLFiniteState s (.while witnessTraversalCondition decodeWitnessNodeIteration)) := by
  have installed : s.code=originalRuntimeCode := by
    obtain ⟨⟨scratch,heap,top,mode,go,state⟩,_⟩ := valid
    exact state.code
  apply rankedWhile_run witnessTraversalCondition decodeWitnessNodeIteration
    (witnessTraversalIterationCost layout.inputLimit) (fun {F} state n=>WitnessTraversalRank layout state n ∧state.memory watched=word) False
    (fun state ranked value condition=>ranked.1.zero_exit layout state value condition) ?_ rank s installed ⟨valid,atWord⟩ budget
  intro G state n word code ranked condition nonzero ticks
  obtain ⟨⟨⟨scratch,heap,top,mode,go,stateValid⟩,rankEq⟩,wordKept⟩ := ranked
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
    have memory := entryValid.iteration_memory_frame layout (decClockHOLFinite state) post scratch heap top mode go entryTicks run watched above below
    exact ⟨witnessTraversalStateMeasure layout.frame post,by omega,⟨⟨kept,rfl⟩,memory.trans wordKept⟩,metadata.1⟩
  · intro broken
    exact False.elim (control.1 broken)


theorem witness_traversal_loop_normal_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalInvariant layout s)
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (.while witnessTraversalCondition decodeWitnessNodeIteration)=(none,post)) :
 ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 intro watched above below
 have ceiling:=witnessTraversalStateMeasure_bound s layout.frame
 have costBound : witnessTraversalStateMeasure layout.frame s*(witnessTraversalIterationCost layout.inputLimit+1)≤witnessTraversalLoopCost layout.inputLimit := Nat.mul_le_mul_right _ (Nat.le_of_lt ceiling)
 have checked:=witness_traversal_ranked_loop_memory layout s watched (s.memory watched) above below
  (witnessTraversalStateMeasure layout.frame s) ⟨valid,rfl⟩ rfl (costBound.trans budget)
 rw [run] at checked
 obtain ⟨rank,⟨_,memory⟩,_,_⟩:=checked.2.2.2 rfl
 exact memory
#print axioms witness_traversal_ranked_loop_memory
#print axioms witness_traversal_loop_normal_memory
end InitECandidate.Runtime
