import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.TxScalarU256InputGlobalFrame
import InitECandidate.Runtime.TxScalarU256IndependentOuterPrefix
import InitECandidate.Runtime.TxScalarU256InputBound
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Scalar-u256 assignment calls retain independently bounded outer input slices. -/
theorem txScalarU256_local_call_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (array index maximum input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum)])
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_scalar_u256") arguments) = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "maxb",.val (.word maximum))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word maximum)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have installed : state.code.lookup (ofString "tx_scalar_u256") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)],sourceFunctionBody Guest.guestFn_tx_scalar_u256,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txScalarU256_lookup
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_u256") (ofString "arr") (ofString "i") (ofString "maxb")
    (sourceFunctionBody Guest.guestFn_tx_scalar_u256) (.comb [.one,.one,.one,.one]) array index maximum (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_scalar_u256")
    (.comb [.one,.one,.one,.one]) arguments _ (sourceFunctionBody Guest.guestFn_tx_scalar_u256) callee args lookup run
  have ticks : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := outerValid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry _ _ _ _ _ _ item rfl rfl rfl⟩
  have retained := txScalarU256_input_returned_independent_outer_prefix entry bodyPost array index maximum input inputLength scratch frame count ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
    outerArray outerCount outerInput outerLength entryOuter outerBelow
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame bodyPost _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms txScalarU256_local_call_outer_prefix
end InitECandidate.Runtime
