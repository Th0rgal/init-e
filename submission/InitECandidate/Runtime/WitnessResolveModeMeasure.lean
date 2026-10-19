import InitECandidate.Runtime.WitnessResolveAllocationStack
import InitECandidate.Runtime.WitnessResolveModeProgress
import InitECandidate.Runtime.WitnessStackChildCreditFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual resolve mode retains physical capacity and child work, then spends
mode credit by handing control to delivery or decoding of an input slice. -/
theorem witness_resolve_mode_measure_decreases {F : Type}
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
    (post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
      post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) top (witnessTraversalChildCredit post top) 1 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 3) ∨
    (post.locals.lookup (ofString "mode")=some (.val (.word (1#64))) ∧
      post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) top (witnessTraversalChildCredit post top) 2 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 3) := by
  obtain ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_resolve_mode_normal_heap_frame
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound heapAligned atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget run
  have childCredit := witness_stack_child_credit_after_frame s post input inputLength heapPointer top persistentFloor ceiling
    (stack.physical s input inputLength heapPointer top persistentFloor ceiling) floorBeforeHeap memory
  obtain ⟨capacity,topPost,control⟩ := witness_resolve_mode_normal_progress
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top ceiling inputLimit atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget run
  rcases control with ⟨modePost,node,resultPost⟩ | ⟨p,n,modePost,pPost,nPost,span⟩
  · refine Or.inl ⟨modePost,topPost.trans atTop,?_⟩
    rw [capacity,childCredit]
    exact decodeWitnessMeasure_mode (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 3 1 (by decide)
  · refine Or.inr ⟨modePost,topPost.trans atTop,?_⟩
    rw [capacity,childCredit]
    exact decodeWitnessMeasure_mode (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 3 2 (by decide)

#print axioms witness_resolve_mode_measure_decreases
end InitECandidate.Runtime
