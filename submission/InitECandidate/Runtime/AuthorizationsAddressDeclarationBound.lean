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

theorem authorization_five_call_entry_budget (work before : Nat)
    (budget : 5 * (work + 92668) ≤ before) : work + 92633 ≤ before - 1 := by omega

theorem authorization_five_call_tail_budget (work before after : Nat)
    (budget : 5 * (work + 92668) ≤ before) (spent : before - 1 ≤ after + (work + 92633)) :
    4 * (work + 92668) ≤ after := by omega

/-- The final five authorization fields, starting at the address
declaration, have a finite original-input source-clock bound. -/
theorem evaluate_authorization_address_declaration_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) (fits : record.toNat + 120 < 2^64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (budget : 5 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state authorizationAddressDeclaration
    state.clock ≤ evaluated.2.clock + 5 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word (1 : BitVec 64)))).update (ofString "width",.val (.word (20 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (1 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "i" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have inside1 : (1 : BitVec 64).toNat < count.toNat := by change 1 < count.toNat; omega
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    exact authorization_five_call_entry_budget _ _ budget
  have bounded := evaluate_txFixedBytes_input_bounded entry array 1 input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 1,.const 20] =
      some [.val (.word array),.val (.word (1 : BitVec 64)),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txFixedBytes_lookup
  rw [← code] at installed
  have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes")
    (ofString "arr") (ofString "i") (ofString "width") (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    array 1 20 (by decide) (by decide) (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    rw [bodyRun] at metadata
    dsimp only at metadata
    have bodyCost : state.clock - 1 ≤ post.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633) := bounded.1
    have positive : 0 < state.clock := by omega
    have callCost : state.clock ≤ post.clock + cost := by dsimp only [cost]; omega
    have tailBudget : 4 * cost ≤ post.clock := authorization_five_call_tail_budget _ _ _ budget bodyCost
    rw [source_authorization_address_declaration]
    have composed := evaluate_decCall_checked_continuation_bounded state post (ofString "addr") (ofString "tx_fixed_bytes")
      .one .one [.rfield 0 (.var .local (ofString "ent")),.const 1,.const 20]
      [.val (.word array),.val (.word (1 : BitVec 64)),.val (.word (20 : BitVec 64))]
      (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) authorizationAddressStore callee result cost (4 * cost)
      args lookup (Nat.ne_of_gt positive) bodyRun bounded.2.1
      callCost bounded.2.2 ?_
    · have costSum : cost + 4 * cost = 5 * cost := by omega
      simpa only [costSum,cost] using composed
    · intro value returned checked
      have retained := txFixedBytes_input_returned_prefix entry post array 1 input inputLength scratch frame count ceiling inputLimit
        atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
        framePositive scratchBelow arena bodyBudget value (by rw [bodyRun]; exact congrArg (fun r => (r,post)) returned) arrayBelowFrame
      have globals := txFixedBytes_input_returned_globals entry post array 1 input inputLength scratch frame count.toNat ceiling inputLimit
        atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
        framePositive scratchBelow arena bodyBudget value (by rw [bodyRun]; exact congrArg (fun r => (r,post)) returned)
      have checkedOne : shapeEqHOL (shapeOfHOLExact value) .one = true := by
        simpa only [Bool.and_self] using checked
      obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checkedOne)
      let resumed := setVarHOLFinite (ofString "addr") (.val (.word word)) {post with locals := state.locals}
      have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
        intro slot inside
        obtain ⟨p,n,item⟩ := retained slot inside
        exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
      have resumedRecord : resumed.locals.lookup (ofString "a") = some (.val (.word record)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "addr" ≠ ofString "a" by decide] using atRecord
      have resumedEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "addr" ≠ ofString "ent" by decide] using entryLocal
      have resumedValue : resumed.locals.lookup (ofString "addr") = some (.val (.word word)) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      exact evaluate_authorization_address_store_bounded resumed record word array count input inputLength
        scratch frame ceiling inputLimit resumedRecord resumedValue before fits resumedEntry resumedPrefix inside inputBound limitBound
        globals.1 globals.2 (metadata.1.trans code) orderedFrame framePositive scratchBelow
        (by change ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → post.memaddrs address
            intro address lower upper
            rw [metadata.2.1]
            exact arena address lower upper) arrayBelowFrame tailBudget

#print axioms evaluate_authorization_address_declaration_bounded
end InitECandidate.Runtime
