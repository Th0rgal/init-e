import InitECandidate.Runtime.RlpSlicesBodyInputPrefix
import InitECandidate.Runtime.RlpSlicesBodyMemoryBetween
import InitECandidate.Runtime.RlpSliceInputPrefixBetween
/- Successful list construction retains an older heap array between the scratch ceiling and the new allocation while establishing bounded new slices. -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_body_returned_heap_input_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock)
    (older olderCount input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state older input inputLength olderCount.toNat)
    (before : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (olderAboveScratch : ceiling ≤ older.toNat)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    ∃ count : BitVec 64, value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ length.toNat ∧
      RlpSliceInputPrefix post array pointer length count.toNat ∧ RlpSliceInputPrefix post older input inputLength olderCount.toNat := by
  obtain ⟨count,shape,bounded,readable,memory⟩ := rlpSlices_body_returned_memory_between state post pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound countLimit heapArena budget value run
  obtain ⟨newCount,newShape,newBound,inputPrefix⟩ := rlpSlices_body_returned_input_prefix state post pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound countLimit heapArena budget inputBeforeFrame inputBeforeArray value run
  have equal : count = newCount := by
    have shapes := shape.symm.trans newShape
    simpa only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true,true_and] using shapes
  subst newCount
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [run] at metadata
  refine ⟨count,shape,bounded,inputPrefix,?_⟩
  exact RlpSliceInputPrefix.after_memory_between state post older olderCount input inputLength array ceiling
    valid olderAboveScratch before metadata.2.1 memory

#print axioms rlpSlices_body_returned_heap_input_contract
end InitECandidate.Runtime
