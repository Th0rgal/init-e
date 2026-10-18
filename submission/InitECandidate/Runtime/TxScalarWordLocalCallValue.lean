import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.OriginalTxScalarWordCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txScalarWord_local_call_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (array index maximum errorCode : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum),.val (.word errorCode)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_scalar_word") arguments) = (none,post)) :
    ∃ word : BitVec 64, post.locals.lookup name = some (.val (.word word)) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := (((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "maxb",.val (.word maximum))).update (ofString "envcode",.val (.word errorCode))
  have installed : state.code.lookup (ofString "tx_scalar_word") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one),(ofString "envcode",.one)],sourceFunctionBody Guest.guestFn_tx_scalar_word,.one) := by
    rw [code]; exact originalRuntimeCode_txScalarWord_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "tx_scalar_word") (ofString "arr") (ofString "i") (ofString "maxb") (ofString "envcode")
    (sourceFunctionBody Guest.guestFn_tx_scalar_word) array index maximum errorCode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_scalar_word")
    .one arguments _ (sourceFunctionBody Guest.guestFn_tx_scalar_word) callee args lookup run
  obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  refine ⟨word,?_⟩
  rw [restored]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms txScalarWord_local_call_value
end InitECandidate.Runtime
