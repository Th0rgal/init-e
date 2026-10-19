import InitECandidate.Runtime.NodedbSetLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def NodedbSliceTargets (array total : BitVec 64) : Set (BitVec 64) :=
  {value | ∃ index : BitVec 64, index.toNat < total.toNat ∧ value = array + index * (16#64)}

theorem nodedb_set_normal_values {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index total output heap : BitVec 64)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned 32 table keys stride capacity used values order orderPos count bits state)
    (ordered : OrderInv state capacity count used order orderPos)
    (atArray : state.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atTable : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (atOutput : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapAligned : heap.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ heap.toNat)
    (heapInside : heap.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (capacityMargin : 2 * total.toNat + 2 ≤ capacity.toNat)
    (occupancy : count.toNat ≤ index.toNat) (active : index.toNat < total.toNat)
    (vt : VTabs (NodedbSliceTargets array total) state capacity count used keys stride values order)
    (oldBelow : orderPos.toNat + capacity.toNat * 8 ≤ heap.toNat)
    (budget : setBodyCost 32 capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") nodedbSetArguments) = (none,post)) :
    ∃ nextCount : BitVec 64,
      HtabAligned 32 table keys stride capacity used values order orderPos nextCount bits post ∧
      OrderInv post capacity nextCount used order orderPos ∧
      VTabs (NodedbSliceTargets array total) post capacity nextCount used keys stride values order ∧
      nextCount.toNat ≤ index.toNat + 1 := by
  obtain ⟨⟨nextCount,nextInv,shape,occupied,room,nextOrder⟩,rest⟩ :=
    nodedb_set_normal_frame state post array index total output heap table keys stride capacity used values order orderPos
      count bits inv ordered atArray atIndex atTable atOutput atHeap heapAligned headerBelow heapInside arena
      capacityMargin occupancy active budget run
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbSetArguments =
      some [.val (.word table),.val (.word output),.val (.word (array + index * (16#64)))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [nodedbSetArguments,nodedbSliceAddress,evalListHOLExact,evalHOLExact,atTable,atArray,atIndex,atOutput,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  have member : array + index * (16#64) ∈ NodedbSliceTargets array total := ⟨index,active,rfl⟩
  obtain ⟨⟨c',k',u',v',o',op',n',b',broadInv,_,outOrder,outVt⟩,rest'⟩ :=
    htabSet_call_normal_vtabs state post _ _ _ 32 table keys stride capacity used values order orderPos count
      output (array + index * (16#64)) heap bits inv args atHeap heapAligned headerBelow heapInside arena ordered
      (by omega) (by decide) (NodedbSliceTargets array total) vt member oldBelow budget run
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := nextInv.unique broadInv
  exact ⟨_,nextInv,nextOrder,outVt,occupied⟩

#print axioms nodedb_set_normal_values
end InitECandidate.Runtime
