import InitECandidate.Runtime.NodedbBodyReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem nodedb_iteration_heap_monotone {F : Type} (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    (s post : PanSemStateFiniteExact 64 F) (index count heap : BitVec 64)
    (valid : NodedbLoopInv c index count heap s) (active : index.toNat < c.total.toNat)
    (budget : nodedbIterationCost c.capacity c.total ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionBody = (none,post))
    (finalHeap : BitVec 64)
    (atFinal : post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap))) :
    heap.toNat ≤ finalHeap.toNat := by
  obtain ⟨source,size,sourceDomain,sizeDomain,sourceCell,sizeCell,small⟩ := valid.slices index active
  have cost := nodedb_iteration_cost_le c.capacity c.total size count small
    (by have := valid.occupancy; omega) g.capacitySmall
  obtain ⟨_,_,_,heapRel,_⟩ := nodedb_insertion_normal_frame s post c.pointer c.pad c.array index c.total source size
    c.output heap c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits
    valid.tableInv valid.ordered valid.stateGlobal valid.padGlobal valid.arrayLocal valid.indexLocal
    valid.tableLocal valid.outputGlobal sourceDomain sizeDomain sourceCell sizeCell small g.outputAligned
    valid.heapGlobal valid.heapAligned valid.headerBelow valid.heapInside valid.arena
    (by have := valid.occupancy; have := g.capacityMargin; omega) g.tableSeparate (cost.trans budget)
    g.capacityMargin valid.occupancy active run
  obtain ⟨h,atHeap,mono,al,cap⟩ := heapRel.2 heap valid.heapGlobal valid.heapAligned valid.heapInside
  have same : h = finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atHeap.symm.trans atFinal)))
  simpa only [same] using mono

#print axioms nodedb_iteration_heap_monotone
end InitECandidate.Runtime
