import InitECandidate.Runtime.TransactionDataSource
import InitECandidate.Runtime.TxBytesItemInputPrefix
import InitECandidate.Runtime.TxBytesItemInputBound
import InitECandidate.Runtime.OriginalTxBytesItemCode
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.TwoWordValueShape
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_data_field_normal_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state transactionDataField = (none,final)) :
    RlpSliceInputPrefix final array input inputLength count.toNat := by
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
  unfold transactionDataField transactionDataArguments at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "data") (ofString "tx_bytes_item") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_tx_bytes_item) transactionDataFinish callee args lookup run
  rw [bodyRun] at bounded
  obtain ⟨pointer,length,shape⟩ := value_two_words_of_checked_shape value checked.1
  subst value
  let resumed := setVarHOLFinite (ofString "data") (.rStruct [.val (.word pointer),.val (.word length)]) {bodyPost with locals := state.locals}
  have atList : resumed.locals.lookup (ofString "data") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_bytes_item)
  rw [bodyRun] at metadata
  have bodyPrefix := txBytesItem_input_returned_prefix entry bodyPost array index input inputLength scratch frame count ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget _ bodyRun arrayBeforeFrame
  have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := bodyPrefix slot within
    exact ⟨p,n,item.after_frame bodyPost resumed array slot p n input inputLength rfl rfl rfl⟩
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "data" ≠ ofString "tx" by decide] using txLocal
  have stored := transaction_pair_finish_input_prefix resumed (ofString "data") tx pointer length 192 200 1 array count input inputLength
    atTx atList resumedPrefix (by change tx.toNat + 192 < array.toNat; omega)
    (by change tx.toNat + 200 < array.toNat; exact headerBefore) (Nat.le_trans arrayBeforeFrame (Nat.le_of_lt frame.isLt))
  change evaluateHOLFiniteState resumed transactionDataFinish = (none,output) at tailRun
  change RlpSliceInputPrefix (evaluateHOLFiniteState resumed transactionDataFinish).2 array input inputLength count.toNat at stored
  rw [tailRun] at stored
  rw [restored]
  intro slot within
  obtain ⟨p,n,item⟩ := stored slot within
  exact ⟨p,n,item.after_frame output _ array slot p n input inputLength rfl rfl rfl⟩

#print axioms transaction_data_field_normal_prefix
end InitECandidate.Runtime
