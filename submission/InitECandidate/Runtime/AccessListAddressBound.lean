import InitECandidate.Runtime.AccessListSlotItemBound
import InitECandidate.Runtime.TxFixedBytesInputGlobalFrame
import InitECandidate.Runtime.AuthorizationsAddressStoreBound
import InitECandidate.Runtime.TxFixedBytesInputBound
import InitECandidate.Runtime.TxFixedBytesInputPrefix
import InitECandidate.Runtime.TxFixedBytesInputGlobals
import InitECandidate.Runtime.OriginalTxFixedBytesCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.AuthorizationsWord2StoreBound
import InitECandidate.Runtime.PanLocalCallContinuationBound
import InitECandidate.Runtime.TxScalarWordInputBound
import InitECandidate.Runtime.TxScalarWordInputPrefix
import InitECandidate.Runtime.TxScalarWordInputGlobals
import InitECandidate.Runtime.OriginalTxScalarWordCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.AuthorizationsWordStoreRSBound
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.TxScalarU256InputPrefix
import InitECandidate.Runtime.TxScalarU256InputGlobals
import InitECandidate.Runtime.AuthorizationsRStoreLastBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.AuthorizationsRTailSource
import InitECandidate.Runtime.FourWordStoreInputPrefix
import InitECandidate.Runtime.AuthorizationsLastScalarBound
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.TxScalarU256DeclarationInputBound
import InitECandidate.Runtime.TxScalarU256InputBound
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_access_address : accessAddress =
    .decCall (ofString "addr") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "ent")),.const 0,.const 20] accessSlotItem := by
  simp only [accessAddress,accessSlotItem,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual address extraction and the remaining record processing have a whole-input clock bound. -/
theorem evaluate_access_address_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 1 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (heapBeforeFrame : heapPointer.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessAddress
    state.clock ≤ evaluated.2.clock + ((inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength.toNat) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word (0 : BitVec 64)))).update (ofString "width",.val (.word (20 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "i" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have inside1 : (0 : BitVec 64).toNat < count.toNat := by change 0 < count.toNat; omega
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    omega
  have bounded := evaluate_txFixedBytes_input_bounded entry array 0 input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 0,.const 20] =
      some [.val (.word array),.val (.word (0 : BitVec 64)),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txFixedBytes_lookup
  rw [← code] at installed
  have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes")
    (ofString "arr") (ofString "i") (ofString "width") (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    array 0 20 (by decide) (by decide) (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) with
  | mk result post =>
    rw [bodyRun] at bounded
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    rw [bodyRun] at metadata
    have tailBudget : accessSlotItemCost inputLength.toNat ≤ post.clock := by
      have spent := bounded.1
      change state.clock - 1 ≤ post.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633) at spent
      omega
    rw [source_access_address]
    refine evaluate_decCall_checked_continuation_bounded state post (ofString "addr") (ofString "tx_fixed_bytes")
      .one .one _ _ (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) accessSlotItem callee result cost
      (accessSlotItemCost inputLength.toNat) args lookup (by have b := bodyBudget; change _ ≤ state.clock - 1 at b; omega)
      bodyRun bounded.2.1 (by have spent := bounded.1; change state.clock - 1 ≤ post.clock + _ at spent; dsimp [cost]; omega) bounded.2.2 ?_
    intro value returned checked
    have actual := bodyRun
    rw [returned] at actual
    have retainedPrefix := txFixedBytes_input_returned_prefix entry post array 0 input inputLength scratch frame count ceiling inputLimit
      atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena bodyBudget value actual arrayBelowFrame
    have globals := txFixedBytes_input_returned_global_frame entry post array 0 input inputLength scratch frame count.toNat ceiling inputLimit
      atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena bodyBudget value actual
    let resumed := setVarHOLFinite (ofString "addr") value {post with locals := state.locals}
    have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
      intro slot within
      obtain ⟨p,n,item⟩ := retainedPrefix slot within
      exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
    have atEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "addr" ≠ ofString "ent" by decide] using entryLocal
    have nextArgs : evalListHOLFinite resumed (h := fun a => Classical.propDecidable (resumed.memaddrs a))
        [.rfield 0 (.var .local (ofString "ent")),.const 1] = some [.val (.word array),.val (.word (1 : BitVec 64))] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atEntry]
    exact evaluate_access_slot_item_bounded resumed array 1 input inputLength scratch frame heapPointer count.toNat ceiling inputLimit
      nextArgs resumedPrefix (by simpa using inside) inputBound limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal)
      (metadata.1.trans code) orderedFrame framePositive scratchBelow
      (by intro address lower upper; change post.memaddrs address; rw [metadata.2.1]; exact arena address lower upper)
      ((globals _).trans heap) heapBound countLimit
      (by intro address lower upper; change post.memaddrs address; rw [metadata.2.1]; exact heapArena address lower upper)
      inputBeforeHeap heapBeforeFrame tailBudget

#print axioms evaluate_access_address_bounded
end InitECandidate.Runtime
