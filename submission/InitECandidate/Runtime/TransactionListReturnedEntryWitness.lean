import InitECandidate.Runtime.TransactionListReturnedRuntimeContract
import InitECandidate.Runtime.TransactionEntryWitness
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_list_returned_entry_witness {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind : BitVec 64) (ceiling inputLimit : Nat)
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
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state (transactionListCallee pointer length)) (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    let resumed := setVarHOLFinite (ofString "lst") value {post with locals := state.locals}
    ∃ count : BitVec 64, value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ inputLength.toNat ∧
      ∃ valid : TransactionDecodeWitness
        (setVarHOLFinite (ofString "k") (.val (.word 0)) (setVarHOLFinite (ofString "arr") (.val (.word array)) resumed))
        array count tx kind input inputLength scratch frame ceiling,
        valid.heap = allocationEnd array (count * 16) ∧
        valid.heap.toNat ≤ array.toNat + inputLength.toNat * 16 + 7 := by
  let resumed := setVarHOLFinite (ofString "lst") value {post with locals := state.locals}
  obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,covered,endpoint,aligned⟩ :=
    transaction_list_returned_runtime_contract state post pointer length scratch frame array input inputLength ceiling inputLimit
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit
      heapArena budget inputBeforeFrame inputBeforeArray starts ends value run
  have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state (transactionListCallee pointer length))
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [run] at metadata
  have domain : post.memaddrs = state.memaddrs := metadata.2.1
  let valid := transaction_decode_entry_witness resumed array count tx kind input inputLength scratch frame
    (allocationEnd array (count * 16)) ceiling
    (by simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "lst" ≠ ofString "tx" by decide] using txLocal)
    (by simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "lst" ≠ ofString "t" by decide] using typeLocal)
    slices scratchPost framePost heapPost (metadata.1.trans code)
    (by intro address low high; change post.memaddrs address; rw [domain]; exact arena address low high)
    (by
      intro address low high
      change post.memaddrs address
      rw [domain]
      apply heapArena address _ high
      omega)
    endpoint aligned (by omega) covered
  have product : (count * 16).toNat = count.toNat * 16 := by
    have fits : count.toNat * (16 : BitVec 64).toNat < 2^64 := by
      change count.toNat * 16 < 2^64
      omega
    exact BitVec.toNat_mul_of_lt fits
  have rounded := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
  have sizeBound := Nat.mul_le_mul_right 16 countBound
  refine ⟨count,shape,countBound,valid,rfl,?_⟩
  change (allocationEnd array (count * 16)).toNat ≤ array.toNat + inputLength.toNat * 16 + 7
  rw [product] at rounded
  omega

#print axioms transaction_list_returned_entry_witness
end InitECandidate.Runtime
