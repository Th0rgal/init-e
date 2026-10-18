import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.OriginalTxToItemCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original scalar assignments install four checked word limbs. -/
theorem txToItem_local_call_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (array index : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "tx_to_item") arguments) = (none,post)) :
    ∃ word : BitVec 64, post.locals.lookup name = some (.val (.word word)) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  have installed : state.code.lookup (ofString "tx_to_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_to_item,.one) := by
    rw [code]; exact originalRuntimeCode_txToItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_to_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_to_item) .one array index (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "tx_to_item")
    .one arguments _ (sourceFunctionBody Guest.guestFn_tx_to_item) callee args lookup run
  obtain ⟨word,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  refine ⟨word,?_⟩
  rw [restored]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms txToItem_local_call_value
end InitECandidate.Runtime
