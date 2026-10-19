import InitECandidate.Runtime.NodedbSuffixReturnedFrame
import InitECandidate.Runtime.HtabUnionSites
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual returned suffix retains the final table invariant in its returned
state, even though return and declaration scope restoration discard loop locals. -/
theorem nodedb_suffix_returned_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) (heap : BitVec 64)
    (entry : NodedbLoopInv c 0 0 heap (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s))
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s (nodedbAt 3) = (some (.returned value),post)) :
    value = .val (.word c.table) ∧ ∃ count finalHeap : BitVec 64,
      count.toNat ≤ c.total.toNat ∧
      HtabAligned 32 c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits post ∧
      OrderInv post c.capacity count c.used c.order c.orderPos ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat % 8 = 0 ∧ c.table.toNat + 72 ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 := by
  obtain ⟨valueEq,middle,index,count,finalHeap,indexEq,loopRun,inv,clockEq,memoryEq,globalsEq,domainEq,
    codeEq,_,_,heapGlobal,aligned,below,bounded,rest⟩ :=
    nodedb_suffix_returned_frame s post value c g heap entry budget run
  have postMeta := evaluateHOLFiniteState_metadata s (nodedbAt 3)
  rw [run] at postMeta
  have middleMeta := evaluateHOLFiniteState_metadata
    (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) nodedbInsertionLoop
  rw [loopRun] at middleMeta
  have endian : post.be = middle.be := postMeta.2.2.1.trans middleMeta.2.2.1.symm
  have room : count.toNat ≤ c.capacity.toNat := by
    have occupied := inv.occupancy
    have margin := g.capacityMargin
    rw [indexEq] at occupied
    omega
  refine ⟨valueEq,count,finalHeap,?_,?_,?_,heapGlobal,aligned,below,bounded⟩
  · simpa only [indexEq] using inv.occupancy
  · exact inv.tableInv.congr domainEq endian codeEq
      (fun _ _ => congrFun memoryEq _) (fun _ _ => congrFun memoryEq _)
  · exact inv.ordered.congr room domainEq endian
      (fun _ _ => congrFun memoryEq _) (fun _ _ => congrFun memoryEq _) (fun _ _ => congrFun memoryEq _)

#print axioms nodedb_suffix_returned_table
end InitECandidate.Runtime
