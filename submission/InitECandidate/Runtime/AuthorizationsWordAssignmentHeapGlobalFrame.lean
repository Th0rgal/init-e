import InitECandidate.Runtime.AuthorizationsWordAssignmentGlobalFrame
import InitECandidate.Runtime.AuthorizationsWordStoreRSHeapGlobalFrame
import InitECandidate.Runtime.TxScalarWordInputGlobalFrame
import InitECandidate.Runtime.PanLocalCallNormalMemoryScope
import InitECandidate.Runtime.TxScalarWordOuterPrefix
import InitECandidate.Runtime.AuthorizationsWordAssignmentHeapBound
import InitECandidate.Runtime.AuthorizationsWordStoreRSHeapOuterPrefix
import InitECandidate.Runtime.PanLocalCallContinuationBound
import InitECandidate.Runtime.TxScalarWordInputBound
import InitECandidate.Runtime.TxScalarWordInputPrefix
import InitECandidate.Runtime.TxScalarWordInputGlobals
import InitECandidate.Runtime.OriginalTxScalarWordCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.AuthorizationsWordStoreRSHeapBound
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.TxScalarU256InputPrefix
import InitECandidate.Runtime.TxScalarU256InputGlobals
import InitECandidate.Runtime.AuthorizationsRStoreLastHeapBound
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
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful assignment-form word extraction and the remaining record fields
preserve every global binding under the three-call budget. -/
theorem authorization_word_assignment_normal_heap_global_frame {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat) (fits : record.toNat + 120 < 2^64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (budget : 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (run : evaluateHOLFiniteState state authorizationWordAssignAndTail = (none,final)) :
    ∀ watched : MlS, final.globals.lookup watched = state.globals.lookup watched := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  let callee := (txScalarWordCallee array 3 1).update (ofString "envcode",.val (.word (12 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "envcode" ≠ ofString "arr" by decide,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (3 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "envcode" ≠ ofString "i" by decide,
      show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word (1 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "envcode" ≠ ofString "maxb" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have inside3 : (3 : BitVec 64).toNat < count.toNat := by change 3 < count.toNat; omega
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92642 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92642 ≤ state.clock - 1
    exact authorization_three_call_entry_budget _ _ budget
  have bounded := evaluate_txScalarWord_input_bounded entry array 3 1 input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside3 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 3,.const 1,.const 12] =
      some [.val (.word array),.val (.word (3 : BitVec 64)),.val (.word (1 : BitVec 64)),.val (.word (12 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txScalarWord_lookup
  rw [← code] at installed
  have lookup := pan_four_word_lookup state.code.lookup (ofString "tx_scalar_word")
    (ofString "arr") (ofString "i") (ofString "maxb") (ofString "envcode") (sourceFunctionBody Guest.guestFn_tx_scalar_word)
    array 3 1 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  rw [source_authorization_word_assignment] at run
  obtain ⟨value,post,bodyRun,checked,tail⟩ := evaluate_localCall_normal_memory_scope state final
    (ofString "w") (ofString "tx_scalar_word") .one _ _
    (sourceFunctionBody Guest.guestFn_tx_scalar_word) authorizationWordStoreAndRS callee args lookup run
  rw [bodyRun] at bounded
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_scalar_word)
  rw [bodyRun] at metadata
  have tailBudget : 2 * cost ≤ post.clock := authorization_three_call_tail_budget _ _ _ budget bounded.1
  have retained := txScalarWord_input_returned_heap_prefix entry post array 3 1 input inputLength scratch frame count ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside3 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget arrayFits arrayAbove value bodyRun
  have globals := txScalarWord_input_returned_globals entry post array 3 1 input inputLength scratch frame count ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside3 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget value bodyRun
  have kept := txScalarWord_input_returned_global_frame entry post array 3 1 input inputLength scratch frame count ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside3 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget value bodyRun
  obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  let resumed := setVarHOLFinite (ofString "w") (.val (.word word)) {post with locals := state.locals}
  have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := retained slot inside
    exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
  have resumedRecord : resumed.locals.lookup (ofString "a") = some (.val (.word record)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "w" ≠ ofString "a" by decide] using atRecord
  have resumedEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "w" ≠ ofString "ent" by decide] using entryLocal
  have resumedValue : resumed.locals.lookup (ofString "w") = some (.val (.word word)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have next := authorization_word_store_and_rs_normal_heap_global_frame resumed final record word array count input inputLength
    scratch frame ceiling inputLimit resumedRecord resumedValue before fits resumedEntry resumedPrefix inside inputBound limitBound
    globals.1 globals.2 (metadata.1.trans code) orderedFrame framePositive scratchBelow
    (by change ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → post.memaddrs address
        intro address lower upper
        rw [metadata.2.1]
        exact arena address lower upper) arrayFits arrayAbove tailBudget tail
  intro watched
  exact (next watched).trans (kept watched)

#print axioms authorization_word_assignment_normal_heap_global_frame
end InitECandidate.Runtime
