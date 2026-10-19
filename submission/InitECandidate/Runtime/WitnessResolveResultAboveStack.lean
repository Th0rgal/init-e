import InitECandidate.Runtime.WitnessResolveAllocationStack
import InitECandidate.Runtime.WitnessResolveCompletedNodeEnvelope
import InitECandidate.Runtime.WitnessResultAboveStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_resolve_mode_result_above_stack {F : Type}
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
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode = (none,post)) :
    post.locals.lookup (ofString "mode")=some (.val (.word (1#64))) ∨
      ∃ node : BitVec 64, post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
        post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        WitnessResultAboveStack post input inputLength top node persistentFloor ceiling := by
  obtain ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_resolve_mode_normal_heap_frame
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound heapAligned atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeResolveMode
  rw [run] at metadata
  have oldStack := stack.after_top_hash_frame s post input inputLength heapPointer heapPointer top persistentFloor ceiling
    floorBeforeHeap (Nat.le_refl _) metadata.2.1 memory
  have result := witness_resolve_mode_completed_node_envelope
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget run
  rcases result with pending | ⟨node,mode,localNode,envelope⟩
  · exact Or.inl pending
  · exact Or.inr ⟨node,mode,localNode,witness_result_above_stack_of_completed post input inputLength heapPointer top node
      persistentFloor ceiling oldStack envelope⟩

#print axioms witness_resolve_mode_result_above_stack
end InitECandidate.Runtime
