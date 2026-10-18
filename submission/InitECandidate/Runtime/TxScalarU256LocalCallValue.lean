import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.FourWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original scalar assignments install four checked word limbs. -/
theorem txScalarU256_local_call_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (array index maximum : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_scalar_u256") arguments) = (none,post)) :
    ∃ first second third fourth : BitVec 64,
      post.locals.lookup name = some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
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
  have installed : state.code.lookup (ofString "tx_scalar_u256") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)],sourceFunctionBody Guest.guestFn_tx_scalar_u256,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txScalarU256_lookup
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_u256") (ofString "arr") (ofString "i") (ofString "maxb")
    (sourceFunctionBody Guest.guestFn_tx_scalar_u256) (.comb [.one,.one,.one,.one]) array index maximum (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_scalar_u256")
    (.comb [.one,.one,.one,.one]) arguments _ (sourceFunctionBody Guest.guestFn_tx_scalar_u256) callee args lookup run
  obtain ⟨first,second,third,fourth,rfl⟩ := value_four_words_of_checked_shape value checked
  refine ⟨first,second,third,fourth,?_⟩
  rw [restored]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms txScalarU256_local_call_value
end InitECandidate.Runtime
