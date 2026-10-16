import InitECandidate.Runtime.HashDeleteMoveScope
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteMoveStores : ProgHOL 64 :=
  .seq (.store (hashOrderAddress (ofString "order") (ofString "moved_pos")) (.var .local (ofString "i")))
    (.seq (.store (hashOrderAddress (ofString "order_pos") (ofString "i")) (.var .local (ofString "moved_pos")))
      (.assign .local (ofString "i") (.var .local (ofString "j"))))

theorem source_hashDelete_move_stores :
    (match hashDeleteMoveBody with
     | .seq _ (.seq _ (.dec _ _ _ body)) => body
     | _ => .skip) = hashDeleteMoveStores := by
  unfold hashDeleteMoveBody hashDeleteAfterHash hashDeleteLoopRest hashDeleteMoveStores
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile]
  rfl

/-- The original movement tail updates both order directions and advances the
hole to j; the scan index itself and source clock remain unchanged. -/
theorem evaluate_hashDelete_move_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (order orderPos hole scan position : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (positionLocal : state.locals.lookup (ofString "moved_pos") = some (.val (.word position)))
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8)) :
    evaluateHOLFiniteState state hashDeleteMoveStores =
      (none,setVarHOLFinite (ofString "i") (.val (.word scan))
        (sourceWriteWord (sourceWriteWord state (order + position * 8) hole) (orderPos + hole * 8) position)) := by
  have first := evaluate_store_word state (order + position * 8) hole
    (hashOrderAddress (ofString "order") (ofString "moved_pos")) (.var .local (ofString "i"))
    (eval_hashOrderAddress state _ _ order position orderLocal positionLocal) holeLocal orderDomain
  let written := sourceWriteWord state (order + position * 8) hole
  have second := evaluate_store_word written (orderPos + hole * 8) position
    (hashOrderAddress (ofString "order_pos") (ofString "i")) (.var .local (ofString "moved_pos"))
    (eval_hashOrderAddress written _ _ orderPos hole reverseLocal holeLocal) positionLocal reverseDomain
  have assign : evaluateHOLFiniteState (sourceWriteWord written (orderPos + hole * 8) position)
      (.assign .local (ofString "i") (.var .local (ofString "j"))) =
      (none,setVarHOLFinite (ofString "i") (.val (.word scan))
        (sourceWriteWord written (orderPos + hole * 8) position)) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,sourceWriteWord,written,scanLocal,
      lookupKvarHOLExact,holeLocal,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]
  unfold hashDeleteMoveStores
  exact evaluate_seq_none first (evaluate_seq_none second assign)

#print axioms source_hashDelete_move_stores
#print axioms evaluate_hashDelete_move_stores
end InitECandidate.Runtime
