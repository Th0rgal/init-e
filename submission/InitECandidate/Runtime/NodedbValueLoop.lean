import InitECandidate.Runtime.NodedbValueLoopInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem NodedbValueLoopInv.decClock {c : NodedbLoopConfig} {index count heap : BitVec 64}
    {F : Type} {s : PanSemStateFiniteExact 64 F} (valid : NodedbValueLoopInv c index count heap s) :
    NodedbValueLoopInv c index count heap (decClockHOLFinite s) :=
  ⟨valid.1.decClock,valid.2.1.transfer rfl rfl rfl,valid.2.2⟩

def NodedbValueLoopRank (c : NodedbLoopConfig) {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ index count heap : BitVec 64, NodedbValueLoopInv c index count heap s ∧ rank = c.total.toNat - index.toNat

theorem nodedb_insertion_value_loop_ranked (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) (windows : NodedbValueWorkspace c) :
    ∀ rank : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      NodedbValueLoopRank c s rank → rank * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock →
      RankedOutcome s nodedbInsertionCondition (rank * (nodedbIterationCost c.capacity c.total + 1))
        (NodedbValueLoopRank c) False (evaluateHOLFiniteState s nodedbInsertionLoop) := by
  have exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), NodedbValueLoopRank c s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) nodedbInsertionCondition =
        some (.val (.word w)) → w = 0 := by
    intro F s ⟨index,count,heap,complete,ranking⟩ w ev
    have v := complete.1
    have inactive : ¬ index.toNat < c.total.toNat := by omega
    rw [eval_nodedb_loop_condition s index c.total v.indexLocal v.totalLocal] at ev
    simpa [inactive] using ev.symm
  apply rankedWhile_run nodedbInsertionCondition nodedbInsertionBody (nodedbIterationCost c.capacity c.total)
    (NodedbValueLoopRank c) False exit
  intro F s rank w code ⟨index,count,heap,complete,ranking⟩ cond nonzero budget
  have v := complete.1
  have active : index.toNat < c.total.toNat := by omega
  have entered := complete.decClock
  have ticks : nodedbIterationCost c.capacity c.total ≤ (decClockHOLFinite s).clock := by
    change _ ≤ s.clock - 1; omega
  have bounded := nodedb_loop_iteration_bounded c g (decClockHOLFinite s) index count heap entered.1 active ticks
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
    obtain ⟨nextCount,nextHeap,nextInv⟩ := nodedb_value_loop_iteration_preserves c g windows (decClockHOLFinite s) post index count heap
      entered active ticks run
    have natural : (index + (1#64)).toNat = index.toNat + 1 := word_add_toNat index 1
      (by have := g.totalSmall; omega)
    refine ⟨c.total.toNat - (index + (1#64)).toNat,?_,?_,meta'.1⟩
    · rw [natural]; omega
    · exact ⟨index + (1#64),nextCount,nextHeap,nextInv,rfl⟩
  · intro impossible
    exact False.elim (controls.1 impossible)

theorem nodedb_insertion_loop_values (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    (windows : NodedbValueWorkspace c) {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (count heap : BitVec 64) (valid : NodedbValueLoopInv c 0 count heap s)
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionLoop = (none,post)) :
    ∃ index nextCount nextHeap : BitVec 64, NodedbValueLoopInv c index nextCount nextHeap post := by
  have ranked : NodedbValueLoopRank c s c.total.toNat := ⟨0,count,heap,valid,by simp⟩
  have outcome := nodedb_insertion_value_loop_ranked c g windows c.total.toNat s valid.1.tableInv.code ranked budget
  rw [run] at outcome
  obtain ⟨rank,⟨index,nextCount,nextHeap,inv,ranking⟩,rest⟩ := outcome.2.2.2 rfl
  exact ⟨index,nextCount,nextHeap,inv⟩

#print axioms nodedb_insertion_value_loop_ranked
#print axioms nodedb_insertion_loop_values
end InitECandidate.Runtime
