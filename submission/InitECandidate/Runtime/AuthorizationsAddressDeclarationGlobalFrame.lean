import InitECandidate.Runtime.AuthorizationsAddressStoreGlobalFrame
import InitECandidate.Runtime.TxFixedBytesInputGlobalFrame
import InitECandidate.Runtime.AuthorizationsAddressStoreOuterPrefix
import InitECandidate.Runtime.AuthorizationsAddressDeclarationBound
import InitECandidate.Runtime.TxFixedBytesOuterPrefix
import InitECandidate.Runtime.AuthorizationsWord2StoreOuterPrefix
import InitECandidate.Runtime.AuthorizationsWord2DeclarationBound
import InitECandidate.Runtime.TxScalarWordOuterPrefix
import InitECandidate.Runtime.AuthorizationsRStoreLastOuterPrefix
import InitECandidate.Runtime.AuthorizationsRScalarBound
import InitECandidate.Runtime.PanDecCallCheckedNormalMemoryScope
import InitECandidate.Runtime.TxScalarWordOuterPrefix
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.AuthorizationsLastStorePrefix
import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.TxScalarWordDeclarationInputBound
import InitECandidate.Runtime.TxScalarWordInputBound
import InitECandidate.Runtime.OriginalTxScalarWordCode
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful address extraction and all later fields preserve every global binding. -/
theorem authorization_address_declaration_normal_global_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (record array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (recordLocal : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat)
    (budget : 5 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (recordFits : record.toNat + 120 < 2^64)
    (run : evaluateHOLFiniteState state authorizationAddressDeclaration = (none,post)) :
    ∀ watched : MlS, post.globals.lookup watched = state.globals.lookup watched := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word (1 : BitVec 64)))).update (ofString "width",.val (.word (20 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (1 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "i" by decide]
  have innerPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    exact authorization_five_call_entry_budget _ _ budget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 1,.const 20] =
      some [.val (.word array),.val (.word (1 : BitVec 64)),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txFixedBytes_lookup
  rw [← code] at installed
  have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes")
    (ofString "arr") (ofString "i") (ofString "width") (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    array 1 20 (by decide) (by decide) (by decide) installed
  rw [source_authorization_address_declaration] at run
  obtain ⟨value,bodyPost,ready,output,bodyRun,checked,locals,memory,globals,clock,domain,endian,readyCode,tail,restored⟩ :=
    evaluate_decCall_checked_normal_memory_scope state post (ofString "addr") (ofString "tx_fixed_bytes")
      .one .one _ _
      (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) authorizationAddressStore callee args lookup run
  have kept := txFixedBytes_input_returned_global_frame entry bodyPost array 1 input inputLength scratch frame count.toNat
    ceiling inputLimit atArray atIndex innerPrefix (by change 1 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
  have retainedInner := txFixedBytes_input_returned_prefix entry bodyPost array 1 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex innerPrefix (by change 1 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun arrayBelowFrame
  have restoredGlobals := txFixedBytes_input_returned_globals entry bodyPost array 1 input inputLength scratch frame count.toNat
    ceiling inputLimit atArray atIndex innerPrefix (by change 1 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
  have bounded := evaluate_txFixedBytes_input_bounded entry array 1 input inputLength scratch frame count.toNat
    ceiling inputLimit atArray atIndex innerPrefix (by change 1 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget
  rw [bodyRun] at bounded
  have tailBudget : 4 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ ready.clock := by
    rw [clock]
    exact authorization_five_call_tail_budget _ _ _ budget bounded.1
  obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked.1)
  let entered := setVarHOLFinite (ofString "addr") (.val (.word word)) ready
  have atRecord : entered.locals.lookup (ofString "a") = some (.val (.word record)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "addr" ≠ ofString "a" by decide] using recordLocal
  have atValue : entered.locals.lookup (ofString "addr") =
      some (.val (.word word)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInner : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := retainedInner slot inside
    exact ⟨p,n,item.after_frame bodyPost entered array slot p n input inputLength domain
      (congrFun memory _) (congrFun memory _)⟩
  have atEntry : entered.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "addr" ≠ ofString "ent" by decide] using entryLocal
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
  rw [bodyRun] at metadata
  have result := authorization_address_store_normal_global_frame entered output record word
    array count input inputLength scratch frame ceiling inputLimit atRecord atValue before recordFits
    atEntry enteredInner inside inputBound limitBound (by simpa only [entered,setVarHOLFinite,globals] using restoredGlobals.1)
    (by simpa only [entered,setVarHOLFinite,globals] using restoredGlobals.2)
    (by change ready.code = originalRuntimeCode; exact readyCode.trans (metadata.1.trans code))
    orderedFrame framePositive scratchBelow
    (by change ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → ready.memaddrs address
        intro address lower upper
        rw [domain,metadata.2.1]
        exact arena address lower upper)
    arrayBelowFrame tailBudget tail
  rw [restored]
  intro watched
  exact (result watched).trans ((congrArg (fun g => g.lookup watched) globals).trans (kept watched))

#print axioms authorization_address_declaration_normal_global_frame
end InitECandidate.Runtime
