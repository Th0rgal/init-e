import InitECandidate.Runtime.NodedbLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Starting at zero, the original loop is bounded in every outcome. -/
theorem runBounded_nodedb_insertion_loop (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (count heap : BitVec 64)
    (valid : NodedbLoopInv c 0 count heap s)
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock) :
    RunBounded s nodedbInsertionLoop (c.total.toNat * (nodedbIterationCost c.capacity c.total + 1)) := by
  have ranked : NodedbLoopRank c s c.total.toNat := ⟨0,count,heap,valid,by simp⟩
  have outcome := nodedb_insertion_loop_ranked c g c.total.toNat s valid.tableInv.code ranked budget
  exact ⟨outcome.1,outcome.2.1,outcome.2.2.1⟩

/-- A normal exit has processed the complete decoded entry count and retains
its concrete table, heap and input invariants. -/
theorem nodedb_insertion_loop_normal_result (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    {F : Type} (s post : PanSemStateFiniteExact 64 F) (count heap : BitVec 64)
    (valid : NodedbLoopInv c 0 count heap s)
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionLoop = (none,post)) :
    ∃ index nextCount nextHeap : BitVec 64,
      NodedbLoopInv c index nextCount nextHeap post ∧ index = c.total := by
  have ranked : NodedbLoopRank c s c.total.toNat := ⟨0,count,heap,valid,by simp⟩
  have outcome := nodedb_insertion_loop_ranked c g c.total.toNat s valid.tableInv.code ranked budget
  rw [run] at outcome
  obtain ⟨rank,⟨index,nextCount,nextHeap,nextInv,ranking⟩,code,exit⟩ := outcome.2.2.2 rfl
  have zero : evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) nodedbInsertionCondition =
      some (.val (.word 0)) := by rcases exit with zero | impossible; exact zero; exact impossible.elim
  rw [eval_nodedb_loop_condition post index c.total nextInv.indexLocal nextInv.totalLocal] at zero
  have finished : ¬ index.toNat < c.total.toNat := by
    intro active; simp [active] at zero
  refine ⟨index,nextCount,nextHeap,nextInv,?_⟩
  apply BitVec.eq_of_toNat_eq
  have := nextInv.indexInside
  omega

#print axioms runBounded_nodedb_insertion_loop
#print axioms nodedb_insertion_loop_normal_result
end InitECandidate.Runtime
