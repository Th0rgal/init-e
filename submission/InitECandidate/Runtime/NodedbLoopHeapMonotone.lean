import InitECandidate.Runtime.NodedbIterationHeapMonotone
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
def NodedbLoopFloorRank (c : NodedbLoopConfig) (floor : Nat)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ index count heap : BitVec 64, NodedbLoopInv c index count heap s ∧
    rank = c.total.toNat - index.toNat ∧ floor ≤ heap.toNat

theorem nodedb_insertion_loop_floor_ranked (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) (floor : Nat) :
    ∀ rank : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      NodedbLoopFloorRank c floor s rank → rank * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock →
      RankedOutcome s nodedbInsertionCondition (rank * (nodedbIterationCost c.capacity c.total + 1))
        (NodedbLoopFloorRank c floor) False (evaluateHOLFiniteState s nodedbInsertionLoop) := by
  have exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), NodedbLoopFloorRank c floor s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) nodedbInsertionCondition =
        some (.val (.word w)) → w = 0 := by
    intro F s ⟨index,count,heap,v,ranking,lower⟩ w ev
    have inactive : ¬ index.toNat < c.total.toNat := by omega
    rw [eval_nodedb_loop_condition s index c.total v.indexLocal v.totalLocal] at ev
    simpa [inactive] using ev.symm
  apply rankedWhile_run nodedbInsertionCondition nodedbInsertionBody (nodedbIterationCost c.capacity c.total)
    (NodedbLoopFloorRank c floor) False exit
  intro F s rank w code ⟨index,count,heap,v,ranking,lower⟩ cond nonzero budget
  have active : index.toNat < c.total.toNat := by omega
  have entered := v.decClock
  have ticks : nodedbIterationCost c.capacity c.total ≤ (decClockHOLFinite s).clock := by
    change _ ≤ s.clock - 1; omega
  have bounded := nodedb_loop_iteration_bounded c g (decClockHOLFinite s) index count heap entered active ticks
  have controls := evaluate_noLoopControl nodedbInsertionBody (by decide) (decClockHOLFinite s)
  have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) nodedbInsertionBody
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
  · intro normal
    have normal' : (evaluateHOLFiniteState (decClockHOLFinite s) nodedbInsertionBody).1 = none := by
      rcases normal with normal | impossible
      · exact normal
      · exact False.elim (controls.2 impossible)
    let post := (evaluateHOLFiniteState (decClockHOLFinite s) nodedbInsertionBody).2
    have run : evaluateHOLFiniteState (decClockHOLFinite s) nodedbInsertionBody = (none,post) := by
      exact Prod.ext normal' rfl
    obtain ⟨nextCount,nextHeap,nextInv⟩ := nodedb_loop_iteration_preserves c g (decClockHOLFinite s) post index count heap
      entered active ticks run
    have natural : (index + (1#64)).toNat = index.toNat + 1 := word_add_toNat index 1
      (by have := g.totalSmall; omega)
    refine ⟨c.total.toNat - (index + (1#64)).toNat,?_,?_,meta'.1⟩
    · rw [natural]; omega
    · exact ⟨index + (1#64),nextCount,nextHeap,nextInv,rfl,lower.trans
        (nodedb_iteration_heap_monotone c g (decClockHOLFinite s) post index count heap entered active ticks run
          nextHeap nextInv.heapGlobal)⟩
  · intro impossible
    exact False.elim (controls.1 impossible)

theorem nodedb_insertion_loop_heap_monotone (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    {F : Type} (s post : PanSemStateFiniteExact 64 F) (count heap : BitVec 64)
    (valid : NodedbLoopInv c 0 count heap s)
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionLoop = (none,post)) :
    ∃ index nextCount nextHeap : BitVec 64, NodedbLoopInv c index nextCount nextHeap post ∧
      heap.toNat ≤ nextHeap.toNat := by
  have ranked : NodedbLoopFloorRank c heap.toNat s c.total.toNat := ⟨0,count,heap,valid,by simp,le_refl _⟩
  have outcome := nodedb_insertion_loop_floor_ranked c g heap.toNat c.total.toNat s valid.tableInv.code ranked budget
  rw [run] at outcome
  obtain ⟨rank,⟨index,nextCount,nextHeap,inv,ranking,lower⟩,rest⟩ := outcome.2.2.2 rfl
  exact ⟨index,nextCount,nextHeap,inv,lower⟩

#print axioms nodedb_insertion_loop_floor_ranked
#print axioms nodedb_insertion_loop_heap_monotone
end InitECandidate.Runtime
