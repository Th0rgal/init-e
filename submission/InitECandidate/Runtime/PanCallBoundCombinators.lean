import InitECandidate.Runtime.PanUniformCalleeCallBound
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A tail call (no destination, no handler) costs its body bound plus the
entry tick in every outcome, including failed arguments or lookup. -/
theorem evaluate_tailCall_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (bodyCost : Nat)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + bodyCost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call none function arguments)
    state.clock ≤ evaluated.2.clock + (bodyCost + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      have bounded := bodies values body callee returnShape lookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + bodyCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at bounded
      have nonzero : state.clock ≠ 0 := by omega
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at bounded
        obtain ⟨spent,kept,safe⟩ := bounded
        change state.clock - 1 ≤ post.clock + bodyCost at spent
        change post.clock ≤ state.clock - 1 at kept
        rw [evaluateHOLFiniteState_call,args]
        dsimp only
        rw [lookup]
        dsimp only
        rw [if_neg nonzero,ran]
        rcases result with _ | (_ | _ | _ | _ | _ | _ | _ | _ | _)
        all_goals first
          | (simp at safe; done)
          | (dsimp only; split <;> ((try simp only [emptyLocalsHOLFinite]); exact ⟨by omega,by omega,by simp⟩))
          | (dsimp only; (try simp only [emptyLocalsHOLFinite]); exact ⟨by omega,by omega,by simpa using safe⟩)

#print axioms evaluate_tailCall_uniform_bounded

/-- A declared call whose callee body and continuation are uniformly bounded
costs their sum plus the entry tick, in every outcome. -/
theorem evaluate_decCall_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (bodyCost tailCost : Nat) (budget : bodyCost + 1 + tailCost ≤ state.clock)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + bodyCost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut)
    (tail : ∀ next : PanSemStateFiniteExact 64 F, next.code = state.code → tailCost ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next continuation).2.clock + tailCost ∧
        (evaluateHOLFiniteState next continuation).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next continuation).1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation)
    state.clock ≤ evaluated.2.clock + (bodyCost + 1 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape function arguments continuation args]
    simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup]
      simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      have bounded := bodies values body callee returnShape lookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + bodyCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at bounded
      have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at bounded meta'
        obtain ⟨spent,kept,safe⟩ := bounded
        change state.clock - 1 ≤ post.clock + bodyCost at spent
        have whole := evaluate_decCall_continuation_bounded state post name function shape returnShape arguments values
          body continuation callee result (bodyCost + 1) tailCost args lookup (by omega) ran kept (by omega) safe
          (by
            intro value _
            apply tail
            · change post.code = state.code
              exact meta'.1
            · change tailCost ≤ post.clock
              omega)
        simpa only [Nat.add_assoc] using whole

#print axioms evaluate_decCall_uniform_bounded
end InitECandidate.Runtime
