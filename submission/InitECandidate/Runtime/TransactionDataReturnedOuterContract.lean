import InitECandidate.Runtime.TransactionDataFieldRuntimeFrame
import InitECandidate.Runtime.TransactionDataScopedBound
import InitECandidate.Runtime.PanDecCallReturnedAppendScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_data_returned_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 200 < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 32) = (some (.returned value),post)) :
    ∃ middle output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle transactionTypedSignature = (some (.returned value),output) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat ∧
      middle.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      middle.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      middle.globals.lookup (ofString "heap_ptr") = state.globals.lookup (ofString "heap_ptr") ∧
      (∀ name, name ≠ ofString "k" → name ≠ ofString "data" → middle.locals.lookup name = state.locals.lookup name) ∧
      middle.locals.lookup (ofString "k") = some (.val (.word (index + 1))) ∧
      middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      state.clock ≤ middle.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) ∧
      middle.clock ≤ state.clock ∧ post.memory = output.memory := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k")] = some [.val (.word array),.val (.word index)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    omega
  have bounded := evaluate_txBytesItem_input_bounded entry array index input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  have installed : state.code.lookup (ofString "tx_bytes_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_bytes_item,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txBytesItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_bytes_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_bytes_item) (.comb [.one,.one]) array index (by decide) installed
  rw [evaluate_transaction_data_scope] at run
  unfold transactionDataScoped at run
  obtain ⟨returned,bodyPost,middle,output,bodyRun,checked,prefixRun,tailRun,fieldRun,restored⟩ :=
    evaluate_decCall_returned_append_scope state post (ofString "data") (ofString "tx_bytes_item")
      (.comb [.one,.one]) (.comb [.one,.one]) transactionDataArguments [.val (.word array),.val (.word index)]
      (sourceFunctionBody Guest.guestFn_tx_bytes_item) transactionDataFinish transactionTypedSignature callee value
      args lookup (by omega) (by rfl) run
  obtain ⟨slices,outer,scratchPost,framePost,heapPost,locals,indexPost,postCode,domain,consumed,remaining⟩ :=
    transaction_data_field_normal_runtime_frame state _ array count index tx input inputLength scratch frame ceiling inputLimit
      arrayLocal indexLocal txLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      arrayBeforeFrame headerBefore budget outerArray outerCount outerInput outerLength outerValid outerBelow beforeTx fieldRun
  have activeSlices : RlpSliceInputPrefix middle array input inputLength count.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := slices slot within
    exact ⟨p,n,item.after_frame _ middle _ _ _ _ _ _ rfl rfl rfl⟩
  have activeOuter : RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := outer slot within
    exact ⟨p,n,item.after_frame _ middle _ _ _ _ _ _ rfl rfl rfl⟩
  change (HolFiniteMapExact.resVarEq middle.locals (ofString "data",state.locals.lookup (ofString "data"))).lookup (ofString "k") = _ at indexPost
  rw [restore_other_local _ (ofString "data") (ofString "k") _ (by decide)] at indexPost
  have activeLocals : ∀ name, name ≠ ofString "k" → name ≠ ofString "data" → middle.locals.lookup name = state.locals.lookup name := by
    intro name notIndex notData
    have same := locals name notIndex
    change (HolFiniteMapExact.resVarEq middle.locals (ofString "data",state.locals.lookup (ofString "data"))).lookup name = _ at same
    rw [restore_other_local _ (ofString "data") name _ notData] at same
    exact same
  exact ⟨middle,output,tailRun,activeSlices,activeOuter,scratchPost,framePost,heapPost,activeLocals,indexPost,postCode,domain,consumed,remaining,by rw [restored]⟩

#print axioms transaction_data_returned_outer_contract
end InitECandidate.Runtime
