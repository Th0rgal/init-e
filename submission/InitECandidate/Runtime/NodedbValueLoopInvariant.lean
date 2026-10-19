import InitECandidate.Runtime.NodedbInsertionValues
import InitECandidate.Runtime.NodedbIterationHeapMonotone
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def NodedbValueLoopInv (c : NodedbLoopConfig) (index count heap : BitVec 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  NodedbLoopInv c index count heap s ∧
  VTabs (NodedbSliceTargets c.array c.total) s c.capacity count c.used c.keys c.stride c.values c.order ∧
  c.orderPos.toNat + c.capacity.toNat * 8 ≤ heap.toNat

def NodedbValueWorkspace (c : NodedbLoopConfig) : Prop :=
  c.pointer.toNat + 200 ≤ c.table.toNat ∧ c.pad.toNat + 136 ≤ c.table.toNat ∧
  c.output.toNat + 32 ≤ c.table.toNat

/-- A real complete iteration preserves witness membership and the table's
allocation frontier together with the original runtime invariant. -/
theorem nodedb_value_loop_iteration_preserves (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    (windows : NodedbValueWorkspace c) {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (index count heap : BitVec 64) (valid : NodedbValueLoopInv c index count heap s)
    (active : index.toNat < c.total.toNat)
    (budget : nodedbIterationCost c.capacity c.total ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionBody = (none,post)) :
    ∃ nextCount nextHeap : BitVec 64, NodedbValueLoopInv c (index + (1#64)) nextCount nextHeap post := by
  obtain ⟨base,vt,extent⟩ := valid
  obtain ⟨source,size,sourceDomain,sizeDomain,sourceCell,sizeCell,small⟩ := base.slices index active
  have cost := nodedb_iteration_cost_le c.capacity c.total size count small
    (by have := base.occupancy; omega) g.capacitySmall
  obtain ⟨nextCount,nextHeap,nextInv⟩ := nodedb_loop_iteration_preserves c g s post index count heap base active budget run
  obtain ⟨valueCount,valueInv,valueOrder,nextVt,occupied⟩ :=
    nodedb_insertion_normal_values s post c.pointer c.pad c.array index c.total source size c.output heap
      c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits base.tableInv base.ordered
      base.stateGlobal base.padGlobal base.arrayLocal base.indexLocal base.tableLocal base.outputGlobal
      sourceDomain sizeDomain sourceCell sizeCell small g.outputAligned base.heapGlobal base.heapAligned
      base.headerBelow base.heapInside base.arena
      (by have := base.occupancy; have := g.capacityMargin; omega) g.tableSeparate vt extent
      windows.1 windows.2.1 windows.2.2 (cost.trans budget) g.capacityMargin base.occupancy active run
  have sameCount : valueCount = nextCount :=
    HolWordLab.word.inj (valueInv.cell24.symm.trans nextInv.tableInv.cell24)
  subst valueCount
  have mono := nodedb_iteration_heap_monotone c g s post index count heap base active budget run
    nextHeap nextInv.heapGlobal
  exact ⟨nextCount,nextHeap,nextInv,nextVt,extent.trans mono⟩

#print axioms nodedb_value_loop_iteration_preserves
end InitECandidate.Runtime
