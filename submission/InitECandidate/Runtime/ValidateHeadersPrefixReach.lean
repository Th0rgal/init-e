import InitECandidate.Runtime.ValidateHeadersGuard
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real header-count guard reaches allocation with the unchanged state
and at most 256 headers, or terminates earlier; it spends no clock ticks. -/
theorem validate_headers_count_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (n : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    Reaches s (validateHeadersAt 0) (fun next => next = s ∧ n.toNat ≤ 256) 0 (validateHeadersAt 1) := by
  classical
  rw [source_validate_headers_guard]
  apply runBounded_seq_reaches s validateHeadersCountGuard (validateHeadersAt 1) _ 0
    (RunBounded.ofProg (ProgBounded.straight validateHeadersCountGuard (by rfl)) code (by omega))
  · intro v
    exact evaluate_noDirectReturn validateHeadersCountGuard (by rfl) s v
  · intro next normal
    have cond := eval_validate_headers_count_condition s n atCount
    by_cases large : 256 < n.toNat
    · simp only [if_pos large] at cond
      have guard : evaluateHOLFiniteState s validateHeadersCountGuard =
          evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 1)) := by
        unfold validateHeadersCountGuard
        rw [evaluateHOLFiniteState_ite]
        rw [show evalHOLExact s.toExact validateHeadersCountCondition = some (.val (.word (1#64))) from cond]
        simp
      have noNormal : (evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 1))).1 ≠ none := by
        rw [evaluateHOLFiniteState_raise]
        split
        · dsimp only; split <;> simp
        · simp
      rw [guard] at normal
      exact False.elim (noNormal (congrArg Prod.fst normal))
    · simp only [if_neg large] at cond
      have guard : evaluateHOLFiniteState s validateHeadersCountGuard = (none,s) := by
        unfold validateHeadersCountGuard
        rw [evaluateHOLFiniteState_ite]
        rw [show evalHOLExact s.toExact validateHeadersCountCondition = some (.val (.word (0#64))) from cond]
        simp [evaluateHOLFiniteState_skip]
      rw [guard] at normal
      exact ⟨(Prod.mk.inj normal).2.symm,by omega⟩

#print axioms validate_headers_count_prefix_reaches
end InitECandidate.Runtime
