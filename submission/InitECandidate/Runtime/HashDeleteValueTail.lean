import InitECandidate.Runtime.HashDeleteMovedPosition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteValueTail : ProgHOL 64 :=
  .seq (.store (hashOrderAddress (ofString "vals") (ofString "i"))
    (.load .one (hashOrderAddress (ofString "vals") (ofString "j")))) hashDeleteMovedPosition

theorem source_hashDelete_value_tail :
    (match hashDeleteMoveBody with | .seq _ tail => tail | _ => .skip) = hashDeleteValueTail := by
  unfold hashDeleteMoveBody hashDeleteAfterHash hashDeleteLoopRest hashDeleteValueTail
    hashDeleteMovedPosition hashDeleteMoveStores
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile]
  rfl

/-- The value copy precedes the reverse-position read. Its separation premise
ensures the read still obtains the scanned entry's original order position. -/
theorem evaluate_hashDelete_value_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (values order orderPos hole scan position value : BitVec 64)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (valueDomain : state.memaddrs (values + scan * 8))
    (valueCell : state.memory (values + scan * 8) = .word value)
    (destinationDomain : state.memaddrs (values + hole * 8))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (separate : orderPos + scan * 8 ≠ values + hole * 8)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8)) :
    let written := sourceWriteWord state (values + hole * 8) value
    let entered := setVarHOLFinite (ofString "moved_pos") (.val (.word position)) written
    let post := setVarHOLFinite (ofString "i") (.val (.word scan))
      (sourceWriteWord (sourceWriteWord entered (order + position * 8) hole) (orderPos + hole * 8) position)
    evaluateHOLFiniteState state hashDeleteValueTail =
      (none,{post with locals := (HolFiniteMapExact.resVarEq post.locals
        (ofString "moved_pos",state.locals.lookup (ofString "moved_pos")))}) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashOrderAddress (ofString "vals") (ofString "j"))) = some (.val (.word value)) := by
    simp [hashOrderAddress,evalHOLExact,evalListHOLExact,valuesLocal,scanLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    exact ⟨valueDomain,valueCell⟩
  have store := evaluate_store_word state (values + hole * 8) value
    (hashOrderAddress (ofString "vals") (ofString "i"))
    (.load .one (hashOrderAddress (ofString "vals") (ofString "j")))
    (eval_hashOrderAddress state _ _ values hole valuesLocal holeLocal) loaded destinationDomain
  let written := sourceWriteWord state (values + hole * 8) value
  have literalSeparate : orderPos + scan * 8#64 ≠ values + hole * 8#64 := separate
  have positionAfter : written.memory (orderPos + scan * 8) = .word position := by
    simpa [written,sourceWriteWord,literalSeparate] using loadCell
  have tail := evaluate_hashDelete_moved_position written order orderPos hole scan position
    orderLocal reverseLocal holeLocal scanLocal loadDomain positionAfter orderDomain reverseDomain
  unfold hashDeleteValueTail
  exact evaluate_seq_none store tail

#print axioms source_hashDelete_value_tail
#print axioms evaluate_hashDelete_value_tail
end InitECandidate.Runtime
