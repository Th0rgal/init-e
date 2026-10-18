import InitECandidate.Runtime.AuthorizationsCidDeclarationGlobalFrame
import InitECandidate.Runtime.AuthorizationsCidStoreHeapGlobalFrame
import InitECandidate.Runtime.TxScalarU256InputGlobalFrame
import InitECandidate.Runtime.AuthorizationsCidStoreHeapOuterPrefix
import InitECandidate.Runtime.AuthorizationsCidDeclarationHeapBound
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

/-- Successful extraction of all six fields preserves the outer slice array. -/
theorem authorization_cid_declaration_normal_heap_global_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat)
    (budget : 6 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (recordFits : record.toNat + 120 < 2^64)
    (run : evaluateHOLFiniteState state authorizationCidDeclaration = (none,post)) :
    ∀ watched : MlS, post.globals.lookup watched = state.globals.lookup watched := by
  let callee := txScalarWordCallee array 0 32
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have innerPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ state.clock - 1
    exact authorization_six_call_entry_budget _ _ budget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 0,.const 32] =
      some [.val (.word array),.val (.word (0 : BitVec 64)),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txScalarU256_lookup
  rw [← code] at installed
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_u256")
    (ofString "arr") (ofString "i") (ofString "maxb") (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
    (.comb [.one,.one,.one,.one]) array 0 32 (by decide) (by decide) (by decide) installed
  rw [source_authorization_cid_declaration] at run
  obtain ⟨value,bodyPost,ready,output,bodyRun,checked,locals,memory,globals,clock,domain,endian,readyCode,tail,restored⟩ :=
    evaluate_decCall_checked_normal_memory_scope state post (ofString "cid") (ofString "tx_scalar_u256")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_tx_scalar_u256) authorizationCidStore callee args lookup run
  have kept := txScalarU256_input_returned_global_frame entry bodyPost array 0 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 0 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
  have retainedInner := txScalarU256_input_returned_heap_prefix entry bodyPost array 0 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 0 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget arrayFits arrayAbove value bodyRun
  have restoredGlobals := txScalarU256_input_returned_globals entry bodyPost array 0 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 0 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
  have bounded := evaluate_txScalarU256_input_bounded entry array 0 32 input inputLength scratch frame count.toNat
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by change 0 < count.toNat; omega) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget
  rw [bodyRun] at bounded
  have tailBudget : 5 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ ready.clock := by
    rw [clock]
    exact authorization_six_call_tail_budget _ _ _ budget bounded.1
  obtain ⟨first,second,third,fourth,rfl⟩ := value_four_words_of_checked_shape value checked.1
  let entered := setVarHOLFinite (ofString "cid")
    (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) ready
  have atRecord : entered.locals.lookup (ofString "a") = some (.val (.word record)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "cid" ≠ ofString "a" by decide] using recordLocal
  have atValue : entered.locals.lookup (ofString "cid") =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInner : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := retainedInner slot inside
    exact ⟨p,n,item.after_frame bodyPost entered array slot p n input inputLength domain
      (congrFun memory _) (congrFun memory _)⟩
  have atEntry : entered.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "cid" ≠ ofString "ent" by decide] using entryLocal
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
  rw [bodyRun] at metadata
  have result := authorization_cid_store_normal_heap_global_frame entered output record first second third fourth
    array count input inputLength scratch frame ceiling inputLimit atRecord atValue before recordFits
    atEntry enteredInner inside inputBound limitBound (by simpa only [entered,setVarHOLFinite,globals] using restoredGlobals.1)
    (by simpa only [entered,setVarHOLFinite,globals] using restoredGlobals.2)
    (by change ready.code = originalRuntimeCode; exact readyCode.trans (metadata.1.trans code))
    orderedFrame framePositive scratchBelow
    (by change ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → ready.memaddrs address
        intro address lower upper
        rw [domain,metadata.2.1]
        exact arena address lower upper)
    arrayFits arrayAbove tailBudget tail
  rw [restored]
  intro watched
  exact (result watched).trans ((congrArg (fun g => g.lookup watched) globals).trans (kept watched))

#print axioms authorization_cid_declaration_normal_heap_global_frame
end InitECandidate.Runtime
