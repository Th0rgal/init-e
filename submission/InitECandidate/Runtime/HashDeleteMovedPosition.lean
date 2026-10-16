import InitECandidate.Runtime.HashDeleteMoveStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteMovedPosition : ProgHOL 64 :=
  .dec (ofString "moved_pos") .one
    (.load .one (hashOrderAddress (ofString "order_pos") (ofString "j"))) hashDeleteMoveStores

theorem source_hashDelete_moved_position :
    (match hashDeleteMoveBody with
     | .seq _ (.seq _ tail) => tail
     | _ => .skip) = hashDeleteMovedPosition := by
  unfold hashDeleteMoveBody hashDeleteAfterHash hashDeleteLoopRest hashDeleteMovedPosition hashDeleteMoveStores
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile]
  rfl

theorem evaluate_hashDelete_moved_position {F : Type} (state : PanSemStateFiniteExact 64 F)
    (order orderPos hole scan position : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8)) :
    let entered := setVarHOLFinite (ofString "moved_pos") (.val (.word position)) state
    let post := setVarHOLFinite (ofString "i") (.val (.word scan))
      (sourceWriteWord (sourceWriteWord entered (order + position * 8) hole) (orderPos + hole * 8) position)
    evaluateHOLFiniteState state hashDeleteMovedPosition =
      (none,{post with locals := (HolFiniteMapExact.resVarEq post.locals
        (ofString "moved_pos",state.locals.lookup (ofString "moved_pos")))}) := by
  classical
  dsimp only
  let entered := setVarHOLFinite (ofString "moved_pos") (.val (.word position)) state
  have other : ∀ name, name ≠ ofString "moved_pos" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have run := evaluate_hashDelete_move_stores entered order orderPos hole scan position
    ((other _ (by decide)).trans orderLocal) ((other _ (by decide)).trans reverseLocal)
    ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans scanLocal)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) orderDomain reverseDomain
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashOrderAddress (ofString "order_pos") (ofString "j"))) =
      some (.val (.word position)) := by
    simp [hashOrderAddress,evalHOLExact,evalListHOLExact,reverseLocal,scanLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    exact ⟨loadDomain,loadCell⟩
  unfold hashDeleteMovedPosition
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word position))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  dsimp only
  rw [if_pos shape,run]

#print axioms source_hashDelete_moved_position
#print axioms evaluate_hashDelete_moved_position
end InitECandidate.Runtime
