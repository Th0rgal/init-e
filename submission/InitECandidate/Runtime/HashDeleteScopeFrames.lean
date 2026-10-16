import InitECandidate.Runtime.HashDeleteHashMove32
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Leaving decision and hash scopes retains every unrelated local, notably
both scan j and hole i. Saved bindings may be present or absent. -/
theorem hashDelete_scope_exit_local {F : Type} (state entered post : PanSemStateFiniteExact 64 F)
    (name : MlS) (notHash : name ≠ ofString "h")
    (notHome : name ≠ ofString "home") (notMovable : name ≠ ofString "movable") :
    (hashDeleteHashExit state (hashDeleteMoveExit entered post)).locals.lookup name = post.locals.lookup name := by
  unfold hashDeleteHashExit hashDeleteMoveExit
  rw [restore_other_local _ _ name _ notHash,
    restore_other_local _ _ name _ notHome,restore_other_local _ _ name _ notMovable]

/-- Actual scope exits preserve forward/reverse memory invariants together. -/
theorem hashDelete_scope_exit_entries {F : Type} (state entered post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items : BitVec 64)
    (forward : HashOrderEntriesBound order capacity items post)
    (reverse : HashReverseEntriesBound used orderPos capacity items post) :
    HashOrderEntriesBound order capacity items (hashDeleteHashExit state (hashDeleteMoveExit entered post)) ∧
      HashReverseEntriesBound used orderPos capacity items (hashDeleteHashExit state (hashDeleteMoveExit entered post)) := by
  exact ⟨forward.after_memory post _ order capacity items rfl,
    reverse.after_read post _ used orderPos capacity items rfl rfl rfl⟩

theorem hashDelete_scope_exit_scan {F : Type} (state entered post : PanSemStateFiniteExact 64 F) :
    (hashDeleteHashExit state (hashDeleteMoveExit entered post)).locals.lookup (ofString "j") =
      post.locals.lookup (ofString "j") :=
  hashDelete_scope_exit_local state entered post _ (by decide) (by decide) (by decide)

#print axioms hashDelete_scope_exit_local
#print axioms hashDelete_scope_exit_entries
#print axioms hashDelete_scope_exit_scan
end InitECandidate.Runtime
