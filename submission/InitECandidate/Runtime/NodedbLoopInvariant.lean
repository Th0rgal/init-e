import InitECandidate.Runtime.NodedbIterationCost
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

structure NodedbLoopConfig where
  pointer : BitVec 64
  pad : BitVec 64
  array : BitVec 64
  total : BitVec 64
  output : BitVec 64
  table : BitVec 64
  keys : BitVec 64
  stride : BitVec 64
  capacity : BitVec 64
  used : BitVec 64
  values : BitVec 64
  order : BitVec 64
  orderPos : BitVec 64
  bits : Nat

def NodedbProtected (c : NodedbLoopConfig) (w : BitVec 64) : Prop :=
  w.toNat < c.table.toNat ∧ ¬ MWin c.pointer 200 w ∧ ¬ MWin c.pad 136 w ∧ ¬ MWin c.output 32 w

structure NodedbLoopGeometry (c : NodedbLoopConfig) : Prop where
  totalSmall : c.total.toNat ≤ 134217712
  capacitySmall : c.capacity.toNat ≤ 536870912
  capacityMargin : 2 * c.total.toNat + 2 ≤ c.capacity.toNat
  outputAligned : c.output.toNat % 8 = 0
  tableSeparate : ∀ w : BitVec 64, HtabFoot c.table c.capacity c.used c.order c.orderPos w.toNat →
    ¬ MWin c.pointer 200 w ∧ ¬ MWin c.pad 136 w ∧ ¬ MWin c.output 32 w
  sliceProtected : ∀ j : BitVec 64, j.toNat < c.total.toNat →
    NodedbProtected c (c.array + j * (16#64)) ∧ NodedbProtected c (c.array + j * (16#64) + (8#64))

/-- The concrete state facts carried by the original insertion loop. Slice
words are retained for all entries, including entries not yet processed. -/
structure NodedbLoopInv (c : NodedbLoopConfig) (index count heap : BitVec 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  indexLocal : s.locals.lookup (ofString "i") = some (.val (.word index))
  totalLocal : s.locals.lookup (ofString "n") = some (.val (.word c.total))
  arrayLocal : s.locals.lookup (ofString "slice_arr") = some (.val (.word c.array))
  tableLocal : s.locals.lookup (ofString "t") = some (.val (.word c.table))
  stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word c.pointer))
  padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word c.pad))
  outputGlobal : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word c.output))
  heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  heapAligned : heap.toNat % 8 = 0
  headerBelow : c.table.toNat + 72 ≤ heap.toNat
  heapInside : heap.toNat ≤ 33806089496
  indexInside : index.toNat ≤ c.total.toNat
  occupancy : count.toNat ≤ index.toNat
  tableInv : HtabAligned 32 c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits s
  ordered : OrderInv s c.capacity count c.used c.order c.orderPos
  arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → c.table.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a
  slices : ∀ j : BitVec 64, j.toNat < c.total.toNat → ∃ source size : BitVec 64,
    s.memaddrs (c.array + j * (16#64)) ∧ s.memaddrs (c.array + j * (16#64) + (8#64)) ∧
    s.memory (c.array + j * (16#64)) = .word source ∧
    s.memory (c.array + j * (16#64) + (8#64)) = .word size ∧ size.toNat ≤ 134217712

def NodedbLoopRank (c : NodedbLoopConfig) {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ index count heap : BitVec 64, NodedbLoopInv c index count heap s ∧ rank = c.total.toNat - index.toNat

/-- A normal complete iteration preserves the actual loop invariant and advances
its index without 64-bit wrap. No intermediate state invariant is assumed. -/
theorem nodedb_loop_iteration_preserves (c : NodedbLoopConfig) (geometry : NodedbLoopGeometry c)
    {F : Type} (s post : PanSemStateFiniteExact 64 F) (index count heap : BitVec 64)
    (valid : NodedbLoopInv c index count heap s) (active : index.toNat < c.total.toNat)
    (budget : nodedbIterationCost c.capacity c.total ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionBody = (none,post)) :
    ∃ nextCount nextHeap : BitVec 64, NodedbLoopInv c (index + (1#64)) nextCount nextHeap post := by
  obtain ⟨source,size,sourceDomain,sizeDomain,sourceCell,sizeCell,small⟩ := valid.slices index active
  have cost := nodedb_iteration_cost_le c.capacity c.total size count small (by have := valid.occupancy; omega) geometry.capacitySmall
  obtain ⟨⟨nextCount,nextInv,nextOrder,occupied⟩,idx,kept,heapRel,frame⟩ :=
    nodedb_insertion_normal_frame s post c.pointer c.pad c.array index c.total source size c.output heap
      c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits valid.tableInv valid.ordered
      valid.stateGlobal valid.padGlobal valid.arrayLocal valid.indexLocal valid.tableLocal valid.outputGlobal
      sourceDomain sizeDomain sourceCell sizeCell small geometry.outputAligned valid.heapGlobal valid.heapAligned
      valid.headerBelow valid.heapInside valid.arena (by have := valid.occupancy; have := geometry.capacityMargin; omega)
      geometry.tableSeparate (cost.trans budget) geometry.capacityMargin valid.occupancy active run
  obtain ⟨nextHeap,atHeap,monotone,aligned,capped⟩ := heapRel.2 heap valid.heapGlobal valid.heapAligned valid.heapInside
  have indexNat : (index + (1#64)).toNat = index.toNat + 1 := word_add_toNat index 1
    (by have := geometry.totalSmall; omega)
  have meta' := evaluateHOLFiniteState_metadata s nodedbInsertionBody
  rw [run] at meta'
  have domain : post.memaddrs = s.memaddrs := meta'.2.1
  refine ⟨nextCount,nextHeap,idx,?_,?_,?_,?_,?_,?_,atHeap,aligned,?_,capped,?_,?_,nextInv,nextOrder,?_,?_⟩
  · exact (kept _ (by decide)).trans valid.totalLocal
  · exact (kept _ (by decide)).trans valid.arrayLocal
  · exact (kept _ (by decide)).trans valid.tableLocal
  · exact (heapRel.1 _ (by decide)).trans valid.stateGlobal
  · exact (heapRel.1 _ (by decide)).trans valid.padGlobal
  · exact (heapRel.1 _ (by decide)).trans valid.outputGlobal
  · have := valid.headerBelow; omega
  · rw [indexNat]; omega
  · rw [indexNat]; exact occupied
  · intro a h1 h2 h3
    rw [domain]; exact valid.arena a h1 h2 h3
  · intro j inside
    obtain ⟨src,len,sd,ld,sc,lc,small⟩ := valid.slices j inside
    obtain ⟨p,l⟩ := geometry.sliceProtected j inside
    have preserve (w : BitVec 64) (h : NodedbProtected c w) : post.memory w = s.memory w :=
      frame w h.1 h.2.1 h.2.2.1 h.2.2.2
    refine ⟨src,len,?_,?_,(preserve _ p).trans sc,(preserve _ l).trans lc,small⟩
    · rw [domain]; exact sd
    · rw [domain]; exact ld

#print axioms nodedb_loop_iteration_preserves
end InitECandidate.Runtime
