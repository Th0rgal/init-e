import InitECandidate.Runtime.HashDeleteMoveScope
import InitECandidate.Runtime.HashReverseEntriesBound
import InitECandidate.Runtime.HashOrderEntriesAppend
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashDeleteMoveEntry {F : Type} (state : PanSemStateFiniteExact 64 F) (hash capacity : BitVec 64) :=
  setVarHOLFinite (ofString "movable") (.val (.word (1 : BitVec 64)))
    (setVarHOLFinite (ofString "movable") (.val (.word (0 : BitVec 64)))
      (setVarHOLFinite (ofString "home") (.val (.word (hash &&& (capacity - 1)))) state))

def hashDeleteMoveExit {F : Type} (state post : PanSemStateFiniteExact 64 F) :=
  {post with locals := (HolFiniteMapExact.resVarEq
    (HolFiniteMapExact.resVarEq post.locals (ofString "movable",state.locals.lookup (ofString "movable")))
    (ofString "home",state.locals.lookup (ofString "home")))}

/-- A successful actual movement-body run composes with the original home
and movable scopes, restoring both saved local bindings. -/
theorem evaluate_hashDelete_move_scope_run {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (hole scan hash capacity : BitVec 64)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (moves : hashDeleteMoveRequired hole scan (hash &&& (capacity - 1)))
    (run : evaluateHOLFiniteState (hashDeleteMoveEntry state hash capacity) hashDeleteMoveBody = (none,post)) :
    evaluateHOLFiniteState state hashDeleteAfterHash = (none,hashDeleteMoveExit state post) := by
  rw [evaluate_hashDelete_move_scope state hole scan hash capacity holeLocal scanLocal hashLocal capacityLocal]
  dsimp only
  rw [if_pos moves,if_pos moves]
  unfold hashDeleteMoveEntry at run
  rw [run]
  rfl

/-- Scope restoration changes no table memory or occupancy reads. -/
theorem hashDeleteMoveExit_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items : BitVec 64)
    (forward : HashOrderEntriesBound order capacity items post)
    (reverse : HashReverseEntriesBound used orderPos capacity items post) :
    HashOrderEntriesBound order capacity items (hashDeleteMoveExit state post) ∧
      HashReverseEntriesBound used orderPos capacity items (hashDeleteMoveExit state post) := by
  exact ⟨forward.after_memory post _ order capacity items rfl,
    reverse.after_read post _ used orderPos capacity items rfl rfl rfl⟩

#print axioms evaluate_hashDelete_move_scope_run
#print axioms hashDeleteMoveExit_entries
end InitECandidate.Runtime
