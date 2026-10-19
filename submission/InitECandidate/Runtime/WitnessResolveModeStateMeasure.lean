import InitECandidate.Runtime.WitnessResolveModeMeasure
import InitECandidate.Runtime.WitnessTraversalStateMeasure
import InitECandidate.Runtime.WitnessModeCallerLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_resolve_mode_state_measure_decreases {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer : BitVec 64)
    (ceiling inputLimit : Nat)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (heapAligned : heapPointer.toNat%8=0)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word childArray)
    (atSlot : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (slice : RlpSliceEntry s childArray slot pointer length)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (built : NodedbTableAt s table dbHeap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (arrayEnd : array.toNat + total.toNat*16 ≤ dbHeap.toNat)
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanSize : length.toNat ≤ inputLength.toNat)
    (budget : resolveStepBodyCost length.toNat + 1 ≤ s.clock)
    (persistentFloor : Nat) (floorBeforeHeap : persistentFloor≤heapPointer.toNat)
    (stack : WitnessAllocationStack s input inputLength heapPointer persistentFloor ceiling top)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (oldMode : s.locals.lookup (ofString "mode")=some (.val (.word (2#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode = (none,post)) : witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  have rank := witness_resolve_mode_measure_decreases s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound heapAligned atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget persistentFloor floorBeforeHeap stack run
  have postRunning := (witness_resolve_go_normal_kept s post run).trans running
  have before := witnessTraversalStateMeasure_running s frame top running atTop
  rw [witnessTraversalModeCredit_resolve s oldMode] at before
  rcases rank with ⟨mode,topPost,decreases⟩ | ⟨mode,topPost,decreases⟩
  · have after := witnessTraversalStateMeasure_running post frame top postRunning topPost
    rw [witnessTraversalModeCredit_delivery post mode] at after
    rw [before,after]
    exact decreases
  · have after := witnessTraversalStateMeasure_running post frame top postRunning topPost
    rw [witnessTraversalModeCredit_decode post mode] at after
    rw [before,after]
    exact decreases

#print axioms witness_resolve_mode_state_measure_decreases
end InitECandidate.Runtime
