import InitECandidate.Runtime.HashDeleteFinalSource
import InitECandidate.Runtime.HashDeleteMoveStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteCountReturn : ProgHOL 64 :=
  .seq (.store (hashLocalAddress (ofString "t") 24) (.var .local (ofString "last_pos"))) (.return (.const 1))

theorem source_hashDelete_count_return :
    (match hashDeleteCountTail with
     | .dec _ _ _ (.dec _ _ _ (.seq _ tail)) => tail
     | _ => .skip) = hashDeleteCountReturn := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteCountReturn
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

/-- The final original store writes the decremented count and returns success,
without spending a source call/loop clock. -/
theorem evaluate_hashDelete_count_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table lastPosition : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (lastLocal : state.locals.lookup (ofString "last_pos") = some (.val (.word lastPosition)))
    (domain : state.memaddrs (table + 24)) :
    evaluateHOLFiniteState state hashDeleteCountReturn =
      (some (.returned (.val (.word (1 : BitVec 64)))),emptyLocalsHOLFinite (sourceWriteWord state (table + 24) lastPosition)) := by
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (hashLocalAddress (ofString "t") 24) = some (.val (.word (table + 24))) := by
    simp [hashLocalAddress,evalHOLExact,evalListHOLExact,tableLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have store := evaluate_store_word state (table + 24) lastPosition (hashLocalAddress (ofString "t") 24)
    (.var .local (ofString "last_pos")) address lastLocal domain
  have returned : evaluateHOLFiniteState (sourceWriteWord state (table + 24) lastPosition) (.return (.const 1)) =
      (some (.returned (.val (.word (1 : BitVec 64)))),emptyLocalsHOLFinite (sourceWriteWord state (table + 24) lastPosition)) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  unfold hashDeleteCountReturn
  exact evaluate_seq_none store returned

#print axioms source_hashDelete_count_return
#print axioms evaluate_hashDelete_count_return
end InitECandidate.Runtime
