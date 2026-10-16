import InitECandidate.Runtime.HashDeleteMoveDecision
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteMoveBody : ProgHOL 64 :=
  match hashDeleteAfterHash with
  | .dec _ _ _ (.dec _ _ _ (.seq _ (.ite _ body _))) => body
  | _ => .skip

theorem source_hashDelete_move_scope : hashDeleteAfterHash =
    .dec (ofString "home") .one
      (.op .and [.var .local (ofString "h"),.op .sub [.var .local (ofString "cap"),.const 1]])
      (.dec (ofString "movable") .one (.const 0)
        (.seq hashDeleteMoveDecision
          (.ite (.cmp .notEqual (.var .local (ofString "movable")) (.const 0)) hashDeleteMoveBody .skip))) := by
  unfold hashDeleteMoveBody hashDeleteMoveDecision hashDeleteAfterHash hashDeleteLoopRest
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile]
  rfl

/-- The selected movement body is the source memcpy followed by value and
order updates, with the real local-scope restorations retained. -/
theorem evaluate_hashDelete_move_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hole scan hash capacity : BitVec 64)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    let home := hash &&& (capacity - 1)
    let entered := setVarHOLFinite (ofString "movable") (.val (.word (0 : BitVec 64)))
      (setVarHOLFinite (ofString "home") (.val (.word home)) state)
    let selected := if hashDeleteMoveRequired hole scan home then
      setVarHOLFinite (ofString "movable") (.val (.word (1 : BitVec 64))) entered else entered
    let output := evaluateHOLFiniteState selected
      (if hashDeleteMoveRequired hole scan home then hashDeleteMoveBody else .skip)
    evaluateHOLFiniteState state hashDeleteAfterHash =
      (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq output.2.locals (ofString "movable",state.locals.lookup (ofString "movable")))
        (ofString "home",state.locals.lookup (ofString "home")))}) := by
  classical
  dsimp only
  let home := hash &&& (capacity - 1)
  let homeState := setVarHOLFinite (ofString "home") (.val (.word home)) state
  let entered := setVarHOLFinite (ofString "movable") (.val (.word (0 : BitVec 64))) homeState
  have others : ∀ name, name ≠ ofString "movable" → name ≠ ofString "home" →
      entered.locals.lookup name = state.locals.lookup name := by
    intro name nm nh
    simp [entered,homeState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nm,Ne.symm nh]
  have distinct : ofString "movable" ≠ ofString "home" := by decide
  have decision := evaluate_hashDelete_move_decision entered hole scan home
    ((others _ (by decide) (by decide)).trans holeLocal)
    ((others _ (by decide) (by decide)).trans scanLocal)
    (by simp [entered,homeState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,home,distinct])
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.var .local (ofString "h"),.op .sub [.var .local (ofString "cap"),.const 1]]) =
      some (.val (.word home)) := by
    simp [evalHOLExact,evalListHOLExact,hashLocal,capacityLocal,wordOpHOL,wordOp,
      valueIsWord,valueWord,home]
    change hash &&& ((capacity - 1) &&& BitVec.allOnes 64) = hash &&& (capacity - 1)
    rw [BitVec.and_allOnes]
  have shape (word : BitVec 64) : shapeEqHOL .one (shapeOfHOLExact (.val (.word word))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [source_hashDelete_move_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  rw [if_pos (shape home),evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [evalHOLExact]
  dsimp only
  rw [if_pos (shape 0)]
  rw [evaluateHOLFiniteState_seq_line780,decision]
  by_cases moves : hashDeleteMoveRequired hole scan home <;>
    dsimp only [home] at moves <;>
    simp_all [evaluateHOLFiniteState_ite,evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL,
      entered,homeState,home,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,Ne.symm distinct]

#print axioms source_hashDelete_move_scope
#print axioms evaluate_hashDelete_move_scope
end InitECandidate.Runtime
