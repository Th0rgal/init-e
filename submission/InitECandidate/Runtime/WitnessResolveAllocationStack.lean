import InitECandidate.Runtime.WitnessResolveModeHeapFrame
import InitECandidate.Runtime.WitnessAllocationStackHashFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual resolver call and hash-field update preserve the full physical
stack, its saved links and every retained original-input slice table. -/
theorem witness_resolve_mode_normal_allocation_stack {F : Type}
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
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
      ∃ nextHeap : BitVec 64,
        post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
        heapPointer.toNat≤nextHeap.toNat ∧ nextHeap.toNat≤33806089496 ∧ nextHeap.toNat%8=0 ∧
        WitnessAllocationStack post input inputLength nextHeap persistentFloor ceiling top := by
  obtain ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_resolve_mode_normal_heap_frame
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound heapAligned atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeResolveMode
  rw [run] at metadata
  exact ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,
    stack.after_top_hash_frame s post input inputLength heapPointer nextHeap top persistentFloor ceiling
      floorBeforeHeap growth metadata.2.1 memory⟩

#print axioms witness_resolve_mode_normal_allocation_stack
end InitECandidate.Runtime
