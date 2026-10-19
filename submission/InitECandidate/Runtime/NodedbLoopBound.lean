import InitECandidate.Runtime.NodedbLoopInvariant
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem NodedbLoopInv.decClock {c : NodedbLoopConfig} {index count heap : BitVec 64}
    {F : Type} {s : PanSemStateFiniteExact 64 F} (v : NodedbLoopInv c index count heap s) :
    NodedbLoopInv c index count heap (decClockHOLFinite s) :=
  ⟨v.indexLocal,v.totalLocal,v.arrayLocal,v.tableLocal,v.stateGlobal,v.padGlobal,v.outputGlobal,v.heapGlobal,
    v.heapAligned,v.headerBelow,v.heapInside,v.indexInside,v.occupancy,v.tableInv.transfer rfl rfl rfl rfl,
    v.ordered.transfer rfl rfl rfl,v.arena,v.slices⟩

theorem nodedb_loop_iteration_bounded (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (index count heap : BitVec 64)
    (v : NodedbLoopInv c index count heap s) (active : index.toNat < c.total.toNat)
    (budget : nodedbIterationCost c.capacity c.total ≤ s.clock) :
    RunBounded s nodedbInsertionBody (nodedbIterationCost c.capacity c.total) := by
  obtain ⟨source,size,sd,ld,sc,lc,small⟩ := v.slices index active
  have cost := nodedb_iteration_cost_le c.capacity c.total size count small (by have := v.occupancy; omega) g.capacitySmall
  exact (runBounded_nodedb_insertion_body s c.pointer c.pad c.array index source size c.output heap
    c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits v.tableInv v.ordered
    v.stateGlobal v.padGlobal v.arrayLocal v.indexLocal v.tableLocal v.outputGlobal sd ld sc lc small g.outputAligned
    v.heapGlobal v.heapAligned v.headerBelow v.heapInside v.arena
    (by have := v.occupancy; have := g.capacityMargin; omega) g.tableSeparate (cost.trans budget)).weaken cost

theorem eval_nodedb_loop_condition {F : Type} (s : PanSemStateFiniteExact 64 F) (index total : BitVec 64)
    (idx : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (n : s.locals.lookup (ofString "n") = some (.val (.word total))) :
    evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) nodedbInsertionCondition =
      some (.val (.word (if index.toNat < total.toNat then 1 else 0))) := by
  simp [evalHOLFinite_eq_toExact,nodedbInsertionCondition,evalHOLExact,idx,n,
    Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- The original complete insertion loop has a finite bound for every outcome,
using the decoded count as rank and preserving the concrete invariant on exit. -/
theorem nodedb_insertion_loop_ranked (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) :
    ∀ rank : Nat, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      NodedbLoopRank c s rank → rank * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock →
      RankedOutcome s nodedbInsertionCondition (rank * (nodedbIterationCost c.capacity c.total + 1))
        (NodedbLoopRank c) False (evaluateHOLFiniteState s nodedbInsertionLoop) := by
  have exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), NodedbLoopRank c s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) nodedbInsertionCondition =
        some (.val (.word w)) → w = 0 := by
    intro F s ⟨index,count,heap,v,ranking⟩ w ev
    have inactive : ¬ index.toNat < c.total.toNat := by omega
    rw [eval_nodedb_loop_condition s index c.total v.indexLocal v.totalLocal] at ev
    simpa [inactive] using ev.symm
  apply rankedWhile_run nodedbInsertionCondition nodedbInsertionBody (nodedbIterationCost c.capacity c.total)
    (NodedbLoopRank c) False exit
  intro F s rank w code ⟨index,count,heap,v,ranking⟩ cond nonzero budget
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
    · exact ⟨index + (1#64),nextCount,nextHeap,nextInv,rfl⟩
  · intro impossible
    exact False.elim (controls.1 impossible)

#print axioms nodedb_loop_iteration_bounded
#print axioms nodedb_insertion_loop_ranked
end InitECandidate.Runtime
