import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Compose a call body budget with its real exception handler budget.
Exception-name mismatch, missing shapes and invalid handler bindings terminate
within the same bound. -/
theorem evaluate_handled_call_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function handlerId handlerVar : MlS)
    (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64)) (bodyCost handlerCost : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (bound : state.clock ≤ post.clock + bodyCost) (remaining : post.clock ≤ state.clock)
    (noTimeout : result ≠ some .timeOut)
    (handlerBound : ∀ value, result = some (.exception handlerId value) →
      let resumed := setVarHOLFinite handlerVar value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed handler
      resumed.clock ≤ evaluated.2.clock + handlerCost ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,some (handlerId,handlerVar,handler))) function arguments)
    state.clock ≤ evaluated.2.clock + (bodyCost + handlerCost) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  cases result with
  | none => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
  | some result =>
    cases result with
    | returned value =>
      simp only
      split
      · cases destination with
        | none => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
        | some destination =>
          rcases destination with ⟨kind,name⟩
          dsimp only
          split <;> cases kind <;>
            exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,
              by exact remaining,by simp⟩
      · exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | timeOut => exact False.elim (noTimeout rfl)
    | error => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | «break» => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | «continue» => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | finalFfi ffi => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | exception exceptionId value =>
      simp only
      by_cases equal : exceptionId = handlerId
      · subst exceptionId
        rw [if_pos rfl]
        cases shape : state.eshapes.lookup handlerId with
        | none => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
        | some declared =>
          simp only
          split
          · have tail := handlerBound value rfl
            change post.clock ≤ _ + handlerCost ∧ _ ≤ post.clock ∧ _ at tail
            exact ⟨by omega,by omega,tail.2.2⟩
          · exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
      · rw [if_neg equal]
        exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩

#print axioms evaluate_handled_call_bounded
end InitECandidate.Runtime
