import InitECandidate.Runtime.HashDeleteMoveScope
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original decision scopes leave the entire state unchanged when the
cluster rule says not to move the scanned entry. -/
theorem evaluate_hashDelete_no_move {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hole scan hash capacity : BitVec 64)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (noMove : ¬ hashDeleteMoveRequired hole scan (hash &&& (capacity - 1))) :
    evaluateHOLFiniteState state hashDeleteAfterHash = (none,state) := by
  rw [evaluate_hashDelete_move_scope state hole scan hash capacity holeLocal scanLocal hashLocal capacityLocal]
  simp only [if_neg noMove,evaluateHOLFiniteState_skip]
  let homeState := setVarHOLFinite (ofString "home") (.val (.word (hash &&& (capacity - 1)))) state
  have distinct : ofString "home" ≠ ofString "movable" := by decide
  have saved : homeState.locals.lookup (ofString "movable") = state.locals.lookup (ofString "movable") := by
    simp [homeState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct]
  have restored := restore_setVar_state homeState (ofString "movable") (.val (.word (0 : BitVec 64)))
  rw [saved] at restored
  have final := restore_setVar_state state (ofString "home") (.val (.word (hash &&& (capacity - 1))))
  have inner := congrArg (fun post : PanSemStateFiniteExact 64 F =>
    {post with locals := (HolFiniteMapExact.resVarEq post.locals
      (ofString "home",state.locals.lookup (ofString "home")))}) restored
  rw [final] at inner
  exact congrArg (fun post => (none,post)) inner

#print axioms evaluate_hashDelete_no_move
end InitECandidate.Runtime
