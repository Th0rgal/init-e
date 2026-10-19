import InitECandidate.Runtime.NodedbInsertionHash
import InitECandidate.Runtime.HtabSetNoGrowth
import InitECandidate.Runtime.HtabValueTrack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual node-database insertion call keeps its original capacity and
arrays. Occupancy stays below the next loop index, so the decoded entry count
continues to provide a strict capacity margin. -/
theorem nodedb_set_normal_layout {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index total output heap : BitVec 64)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned 32 table keys stride capacity used values order orderPos count bits state)
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
    (budget : setBodyCost 32 capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") nodedbSetArguments) = (none,post)) :
    (∃ count' : BitVec 64,
      HtabAligned 32 table keys stride capacity used values order orderPos count' bits post ∧
      (count' = count ∨ count'.toNat = count.toNat + 1) ∧
      count'.toNat ≤ index.toNat + 1 ∧ count'.toNat < capacity.toNat) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbSetArguments =
      some [.val (.word table),.val (.word output),.val (.word (array + index * (16#64)))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [nodedbSetArguments,nodedbSliceAddress,evalListHOLExact,evalHOLExact,atTable,atArray,atIndex,atOutput,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  obtain ⟨⟨nextCount,nextInv,shape⟩,locals,domain,endian⟩ := htabSet_call_normal_no_growth state post
    _ _ _ 32 table keys stride capacity used values order orderPos count output (array + index * (16#64)) heap bits
    inv args atHeap heapAligned headerBelow heapInside arena (by omega) (by decide) (by omega) budget run
  refine ⟨⟨nextCount,nextInv,shape,?_,?_⟩,locals,domain,endian⟩
  · rcases shape with same | inc
    · rw [same]; omega
    · omega
  · rcases shape with same | inc
    · rw [same]; omega
    · omega

theorem nodedb_set_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : setBodyCost 32 capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") nodedbSetArguments) = (none,post)) :
    (∃ count' : BitVec 64,
      HtabAligned 32 table keys stride capacity used values order orderPos count' bits post ∧
      (count' = count ∨ count'.toNat = count.toNat + 1) ∧
      count'.toNat ≤ index.toNat + 1 ∧ count'.toNat < capacity.toNat ∧
      OrderInv post capacity count' used order orderPos) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, w.toNat < table.toNat → post.memory w = state.memory w) := by
  obtain ⟨⟨nextCount,nextInv,shape,occupied,room⟩,locals,domain,endian⟩ :=
    nodedb_set_normal_layout state post array index total output heap table keys stride capacity used values order orderPos count bits
      inv atArray atIndex atTable atOutput atHeap heapAligned headerBelow heapInside arena capacityMargin occupancy active budget run
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbSetArguments =
      some [.val (.word table),.val (.word output),.val (.word (array + index * (16#64)))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [nodedbSetArguments,nodedbSliceAddress,evalListHOLExact,evalHOLExact,atTable,atArray,atIndex,atOutput,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  obtain ⟨⟨c',k',u',v',o',op',n',b',broadInv,_,outOrder⟩,_,_,_,frame⟩ :=
    htabSet_call_normal_frame state post _ _ _ 32 table keys stride capacity used values order orderPos count
      output (array + index * (16#64)) heap bits inv args atHeap heapAligned headerBelow heapInside arena ordered
      (by omega) (by decide) budget run
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := nextInv.unique broadInv
  exact ⟨⟨_,nextInv,shape,occupied,room,outOrder⟩,locals,domain,endian,
    fun w below => frame w (by omega) (Or.inl below)⟩

#print axioms nodedb_set_normal_frame

#print axioms nodedb_set_normal_layout
end InitECandidate.Runtime
