import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.OriginalTxFixedBytesCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original scalar assignments install four checked word limbs. -/
theorem txFixedBytes_local_call_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (array index width : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word width)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_fixed_bytes") arguments) = (none,post)) :
    ∃ word : BitVec 64, post.locals.lookup name = some (.val (.word word)) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "width",.val (.word width))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "width" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "width") = some (.val (.word width)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "tx_fixed_bytes") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "width",.one)],sourceFunctionBody Guest.guestFn_tx_fixed_bytes,.one) := by
    rw [code]; exact originalRuntimeCode_txFixedBytes_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes") (ofString "arr") (ofString "i") (ofString "width")
    (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) array index width (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_fixed_bytes")
    .one arguments _ (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) callee args lookup run
  obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  refine ⟨word,?_⟩
  rw [restored]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms txFixedBytes_local_call_value
end InitECandidate.Runtime
