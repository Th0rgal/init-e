import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.TxToItemInputGlobalFrame
import InitECandidate.Runtime.TxToItemIndependentOuterPrefix
import InitECandidate.Runtime.TxToItemInputBound
import InitECandidate.Runtime.OriginalTxToItemCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Optional-recipient calls preserve independently bounded outer input slices. -/
theorem txToItem_local_call_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (array index input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index)])
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_to_item") arguments) = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have installed : state.code.lookup (ofString "tx_to_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_to_item,.one) := by
    rw [code]; exact originalRuntimeCode_txToItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_to_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_to_item) .one array index (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_to_item")
    (.one) arguments _ (sourceFunctionBody Guest.guestFn_tx_to_item) callee args lookup run
  have ticks : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := outerValid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry _ _ _ _ _ _ item rfl rfl rfl⟩
  have retained := txToItem_input_returned_independent_outer_prefix entry bodyPost array index input inputLength scratch frame count ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
    outerArray outerCount outerInput outerLength entryOuter outerBelow
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame bodyPost _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms txToItem_local_call_outer_prefix
end InitECandidate.Runtime
