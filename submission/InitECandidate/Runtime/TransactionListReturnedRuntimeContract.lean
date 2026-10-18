import InitECandidate.Runtime.TransactionListSource
import InitECandidate.Runtime.RlpSlicesBodyOuterRuntimeContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_list_returned_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength : BitVec 64) (ceiling inputLimit : Nat)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state (transactionListCallee pointer length)) (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    let resumed := setVarHOLFinite (ofString "lst") value {post with locals := state.locals}
    ∃ count : BitVec 64, value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ inputLength.toNat ∧
      RlpSliceInputPrefix resumed array input inputLength count.toNat ∧
      resumed.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
      resumed.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      resumed.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      array.toNat + count.toNat * 16 ≤ 33806089496 ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧
      (allocationEnd array (count * 16)).toNat % 8 = 0 := by
  let entry := callEntryStateHOLFinite state (transactionListCallee pointer length)
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,transactionListCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,transactionListCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have ticks : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,covered,endpoint,aligned⟩ :=
    rlpSlices_body_returned_outer_runtime_contract entry post pointer length scratch frame array input inputLength ceiling inputLimit
      atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena heap arrayBound countLimit heapArena ticks inputBeforeFrame inputBeforeArray starts ends value run
  refine ⟨count,shape,countBound,?_,heapPost,scratchPost,framePost,interval,covered,endpoint,aligned⟩
  intro slot inside
  obtain ⟨p,n,item⟩ := slices slot inside
  exact ⟨p,n,item.after_frame post _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms transaction_list_returned_runtime_contract
end InitECandidate.Runtime
