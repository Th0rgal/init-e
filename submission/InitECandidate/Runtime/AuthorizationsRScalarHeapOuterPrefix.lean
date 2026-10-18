import InitECandidate.Runtime.AuthorizationsRScalarOuterPrefix
import InitECandidate.Runtime.AuthorizationsRStoreLastHeapOuterPrefix
import InitECandidate.Runtime.AuthorizationsRScalarHeapBound
import InitECandidate.Runtime.PanDecCallCheckedNormalMemoryScope
import InitECandidate.Runtime.TxScalarU256OuterPrefix
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.AuthorizationsLastStorePrefix
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

/-- Successful final two scalar fields preserve the outer slice array. -/
theorem authorization_r_scalar_normal_heap_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (record array count input inputLength scratch frame outerArray outerCount : BitVec 64) (ceiling inputLimit : Nat)
    (recordLocal : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat)
    (budget : 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray input inputLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64) (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 120 < 2^64)
    (run : evaluateHOLFiniteState state authorizationRScalar = (none,post)) :
    RlpSliceInputPrefix post outerArray input inputLength outerCount.toNat := by
  let callee := txScalarWordCallee array 4 32
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (4 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have innerPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have outerPrefix : RlpSliceInputPrefix entry outerArray input inputLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerValid slot inside
    exact ⟨p,n,item.after_frame state entry outerArray slot p n input inputLength rfl rfl rfl⟩
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ state.clock - 1
    exact authorization_two_call_entry_budget _ _ budget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 4,.const 32] =
      some [.val (.word array),.val (.word (4 : BitVec 64)),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txScalarU256_lookup
  rw [← code] at installed
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_u256")
    (ofString "arr") (ofString "i") (ofString "maxb") (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
    (.comb [.one,.one,.one,.one]) array 4 32 (by decide) (by decide) (by decide) installed
  rw [source_authorization_r_scalar] at run
  obtain ⟨value,bodyPost,ready,output,bodyRun,checked,locals,memory,globals,clock,domain,endian,readyCode,tail,restored⟩ :=
    evaluate_decCall_checked_normal_memory_scope state post (ofString "r") (ofString "tx_scalar_u256")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_tx_scalar_u256) authorizationRStoreAndLast callee args lookup run
  have retained := txScalarU256_input_returned_heap_independent_outer_prefix entry bodyPost array 4 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 4 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
    outerArray outerCount input inputLength outerPrefix outerFits outerAbove
  have retainedInner := txScalarU256_input_returned_heap_prefix entry bodyPost array 4 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 4 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget arrayFits arrayAbove value bodyRun
  have restoredGlobals := txScalarU256_input_returned_globals entry bodyPost array 4 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 4 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
  have bounded := evaluate_txScalarU256_input_bounded entry array 4 32 input inputLength scratch frame count.toNat
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 4 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget
  rw [bodyRun] at bounded
  have tailBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ ready.clock := by
    rw [clock]
    exact authorization_two_call_tail_budget _ _ _ budget bounded.1
  obtain ⟨first,second,third,fourth,rfl⟩ := value_four_words_of_checked_shape value checked.1
  let entered := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) ready
  have enteredPrefix : RlpSliceInputPrefix entered outerArray input inputLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := retained slot inside
    exact ⟨p,n,item.after_frame bodyPost entered outerArray slot p n input inputLength domain
      (congrFun memory _) (congrFun memory _)⟩
  have atRecord : entered.locals.lookup (ofString "a") = some (.val (.word record)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "r" ≠ ofString "a" by decide] using recordLocal
  have atValue : entered.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInner : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := retainedInner slot inside
    exact ⟨p,n,item.after_frame bodyPost entered array slot p n input inputLength domain
      (congrFun memory _) (congrFun memory _)⟩
  have atEntry : entered.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "r" ≠ ofString "ent" by decide] using entryLocal
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
  rw [bodyRun] at metadata
  have result := authorization_r_store_and_last_normal_heap_outer_prefix entered output record first second third fourth
    array count input inputLength scratch frame outerArray outerCount ceiling inputLimit atRecord atValue before recordFits
    atEntry enteredInner inside inputBound limitBound (by simpa only [entered,setVarHOLFinite,globals] using restoredGlobals.1)
    (by simpa only [entered,setVarHOLFinite,globals] using restoredGlobals.2)
    (by change ready.code = originalRuntimeCode; exact readyCode.trans (metadata.1.trans code))
    orderedFrame framePositive scratchBelow
    (by change ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → ready.memaddrs address
        intro address lower upper
        rw [domain,metadata.2.1]
        exact arena address lower upper)
    arrayFits arrayAbove tailBudget enteredPrefix outerFits outerAbove outerBeforeRecord tail
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := result slot inside
  exact ⟨p,n,item.after_frame output _ outerArray slot p n input inputLength rfl rfl rfl⟩

#print axioms authorization_r_scalar_normal_heap_outer_prefix
end InitECandidate.Runtime
