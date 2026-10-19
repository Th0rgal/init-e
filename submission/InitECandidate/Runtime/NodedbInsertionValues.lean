import InitECandidate.Runtime.NodedbInsertionNormalFrame
import InitECandidate.Runtime.NodedbHashValues
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem nodedb_insertion_normal_values {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer pad array index total source size output heap : BitVec 64)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned 32 table keys stride capacity used values order orderPos count bits state)
    (ordered : OrderInv state capacity count used order orderPos)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atArray : state.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atTable : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (atOutput : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (sourceDomain : state.memaddrs (array + index * (16#64)))
    (sizeDomain : state.memaddrs (array + index * (16#64) + (8#64)))
    (sourceCell : state.memory (array + index * (16#64)) = .word source)
    (sizeCell : state.memory (array + index * (16#64) + (8#64)) = .word size)
    (small : size.toNat ≤ 134217712) (outAligned : output.toNat % 8 = 0)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapAligned : heap.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ heap.toNat)
    (heapInside : heap.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat)
    (separate : ∀ watched : BitVec 64, HtabFoot table capacity used order orderPos watched.toNat →
      ¬ MWin pointer 200 watched ∧ ¬ MWin pad 136 watched ∧ ¬ MWin output 32 watched)
    (vt : VTabs (NodedbSliceTargets array total) state capacity count used keys stride values order)
    (oldBelow : orderPos.toNat + capacity.toNat * 8 ≤ heap.toNat)
    (stateBelow : pointer.toNat + 200 ≤ table.toNat) (padBelow : pad.toNat + 136 ≤ table.toNat)
    (outputBelow : output.toNat + 32 ≤ table.toNat)
    (budget : (size.toNat * 20 + 125) + (setBodyCost 32 capacity count + 1) ≤ state.clock)
    (capacityMargin : 2 * total.toNat + 2 ≤ capacity.toNat)
    (occupancy : count.toNat ≤ index.toNat) (active : index.toNat < total.toNat)
    (run : evaluateHOLFiniteState state nodedbInsertionBody = (none,post)) :
    ∃ nextCount : BitVec 64,
      HtabAligned 32 table keys stride capacity used values order orderPos nextCount bits post ∧
      OrderInv post capacity nextCount used order orderPos ∧
      VTabs (NodedbSliceTargets array total) post capacity nextCount used keys stride values order ∧
      nextCount.toNat ≤ index.toNat + 1 := by
  obtain ⟨hashed,hashRun,tailRun⟩ := seq_normal_parts (show evaluateHOLFiniteState state
    (.seq (.call (some (none,none)) (ofString "keccak256") nodedbHashArguments) _) = (none,post) from run)
  obtain ⟨inserted,setRun,assignRun⟩ := seq_normal_parts tailRun
  have args := eval_nodedb_hash_arguments state array index source size output atArray atIndex atOutput
    sourceDomain sizeDomain sourceCell sizeCell
  have tableFrame := keccak_call_htab_frame state pointer pad source size output nodedbHashArguments
    32 table keys stride capacity used values order orderPos count bits inv ordered atState atPad args small (by omega) separate
  rw [hashRun] at tableFrame
  have hashLocals := evaluate_discard_call_success_locals state (ofString "keccak256") nodedbHashArguments (by rw [hashRun])
  have hashGlobals := keccak_call_globals_frame nodedbHashArguments state inv.code
  rw [hashRun] at hashLocals hashGlobals
  change hashed.locals = state.locals at hashLocals
  change hashed.globals = state.globals at hashGlobals
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "keccak256") nodedbHashArguments)
  rw [hashRun] at metadata
  have first := runBounded_nodedb_hash state pointer pad array index source size output inv.code atState atPad
    atArray atIndex atOutput sourceDomain sizeDomain sourceCell sizeCell small outAligned (by omega)
  have cost := first.1
  rw [hashRun] at cost
  change state.clock ≤ hashed.clock + (size.toNat * 20 + 124 + 1) at cost
  have remaining : setBodyCost 32 capacity count + 1 ≤ hashed.clock := by omega
  have vtHashed := nodedb_hash_values state pointer pad source size output nodedbHashArguments table keys stride
    capacity used values order orderPos count bits (NodedbSliceTargets array total) inv ordered vt atState atPad args
    small (by omega) stateBelow padBelow outputBelow
  rw [hashRun] at vtHashed
  obtain ⟨nextCount,nextInv,nextOrder,nextVt,occupied⟩ :=
    nodedb_set_normal_values hashed inserted array index total output heap table keys stride capacity used values
      order orderPos count bits tableFrame.1 tableFrame.2
      (by rw [hashLocals]; exact atArray) (by rw [hashLocals]; exact atIndex)
      (by rw [hashLocals]; exact atTable) (by rw [hashGlobals]; exact atOutput)
      (by rw [hashGlobals]; exact atHeap) heapAligned headerBelow heapInside
      (by intro a h1 h2 h3; rw [metadata.2.1]; exact arena a h1 h2 h3)
      capacityMargin occupancy active vtHashed oldBelow remaining setRun
  have setLocals := evaluate_discard_call_success_locals hashed (ofString "htab_set") nodedbSetArguments
    (by rw [setRun])
  rw [setRun] at setLocals
  have indexBinding : inserted.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [setLocals,hashLocals]; exact atIndex
  have assign := evaluate_local_word_assignment inserted (ofString "i")
    (.op .add [.var .local (ofString "i"),.const 1]) index (index + (1#64)) indexBinding
    (by simp [evalHOLExact,evalListHOLExact,indexBinding,wordOpHOL,wordOp,valueIsWord,valueWord])
  rw [assign] at assignRun
  obtain ⟨_,rfl⟩ := Prod.mk.inj assignRun
  exact ⟨nextCount,nextInv.transfer rfl rfl rfl rfl,nextOrder.transfer rfl rfl rfl,
    nextVt.transfer rfl rfl rfl,occupied⟩

#print axioms nodedb_insertion_normal_values
end InitECandidate.Runtime
