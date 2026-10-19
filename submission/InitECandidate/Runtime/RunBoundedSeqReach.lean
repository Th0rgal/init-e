import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A bounded prefix which cannot return reaches its continuation or aborts.
The continuing state keeps any property derived from its actual normal run. -/
theorem runBounded_seq_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F → Prop) (cost : Nat)
    (bounded : RunBounded state first cost)
    (notReturned : ∀ value, (evaluateHOLFiniteState state first).1 ≠ some (.returned value))
    (normal : ∀ next, evaluateHOLFiniteState state first = (none,next) → predicate next) :
    Reaches state (.seq first tail) predicate cost tail := by
  apply reaches_seq state first tail cost predicate
  unfold RunBounded at bounded
  cases run : evaluateHOLFiniteState state first with
  | mk result next =>
    rw [run] at bounded notReturned
    cases result with
    | none => exact Or.inl ⟨next,normal next run,bounded.1,bounded.2.1,rfl⟩
    | some result =>
      right
      exact ⟨result,rfl,(by intro value eq; exact notReturned value (congrArg some eq)),
        bounded.1,bounded.2.1,(by intro _ eq; exact bounded.2.2 (congrArg some eq))⟩

#print axioms runBounded_seq_reaches
end InitECandidate.Runtime
