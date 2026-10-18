import InitECandidate.Runtime.RlpSlicesBodyGlobals
import InitECandidate.Runtime.RlpSlicesBodyInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_body_returned_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputAligned : pointer.toNat % 8 = 0) (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    ∃ count : BitVec 64, value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ length.toNat ∧
      RlpSliceInputPrefix post array pointer length count.toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      array.toNat + count.toNat * 16 ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat % 8 = 0 := by
  obtain ⟨count,shape,bounded,_,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ := rlpSlices_body_returned_globals
    state post pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena budget value run
  obtain ⟨other,otherShape,_,prefixInput⟩ := rlpSlices_body_returned_input_prefix
    state post pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena budget inputBeforeFrame inputAligned inputBeforeArray value run
  have structures := ValueHOL.rStruct.inj (shape.symm.trans otherShape)
  have fields := List.cons.inj structures
  have countValues := (List.cons.inj fields.2).1
  have counts : count = other := HolWordLab.word.inj (ValueHOL.val.inj countValues)
  refine ⟨count,shape,bounded,?_,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩
  simpa only [counts] using prefixInput

#print axioms rlpSlices_body_returned_runtime_contract
end InitECandidate.Runtime
