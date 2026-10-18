import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.TxScalarWordInputGlobalFrame
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordInputBound
import InitECandidate.Runtime.OriginalTxScalarWordCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful scalar-word assignments preserve any independent outer input slice array above the scratch ceiling. -/
theorem txScalarWord_local_call_heap_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (array index maximum errorCode input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum),.val (.word errorCode)])
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_scalar_word") arguments) = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := (((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "maxb",.val (.word maximum))).update (ofString "envcode",.val (.word errorCode))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "envcode" ≠ ofString "arr" by decide,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "envcode" ≠ ofString "i" by decide,show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word maximum)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "envcode" ≠ ofString "maxb" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have installed : state.code.lookup (ofString "tx_scalar_word") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one),(ofString "envcode",.one)],sourceFunctionBody Guest.guestFn_tx_scalar_word,.one) := by
    rw [code]; exact originalRuntimeCode_txScalarWord_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "tx_scalar_word") (ofString "arr") (ofString "i") (ofString "maxb") (ofString "envcode")
    (sourceFunctionBody Guest.guestFn_tx_scalar_word) array index maximum errorCode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_scalar_word")
    .one arguments _ (sourceFunctionBody Guest.guestFn_tx_scalar_word) callee args lookup run
  have ticks : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92642 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := outerValid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry _ _ _ _ _ _ item rfl rfl rfl⟩
  have retained := txScalarWord_input_returned_heap_independent_outer_prefix entry bodyPost array index maximum input inputLength scratch frame count ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
    outerArray outerCount outerInput outerLength entryOuter outerFits outerAbove
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame bodyPost _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms txScalarWord_local_call_heap_outer_prefix
end InitECandidate.Runtime
