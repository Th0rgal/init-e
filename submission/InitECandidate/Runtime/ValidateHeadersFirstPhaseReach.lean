import InitECandidate.Runtime.ValidateHeadersFirstIndexReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original index declaration and entire first loop reach the actual
second-phase continuation, or terminate within the uniform quadratic budget. -/
theorem validate_headers_first_phase_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode)
    (ready : ValidateHeadersFirstReady e s)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 3)
      (fun post => ValidateHeadersFirstInvariant e post 0 ∧ post.code = s.code)
      (validateHeadersFirstLoopCost e.inputLimit) (validateHeadersAt 5) := by
  have combined := reaches_trans_budget s (validateHeadersAt 3) (validateHeadersAt 4) (validateHeadersAt 5)
    (fun next => ValidateHeadersFirstInvariant e next e.count.toNat ∧ next.code = s.code)
    (fun post => ValidateHeadersFirstInvariant e post 0 ∧ post.code = s.code)
    0 (validateHeadersFirstLoopCost e.inputLimit) (by omega) (validate_headers_first_index_reaches e s ready)
    (by
      intro next facts remaining
      have tailRun := validate_headers_first_loop_reaches e next e.count.toNat (facts.2.trans code) facts.1 remaining
      exact reaches_mono next (validateHeadersAt 4) (validateHeadersAt 5) _ _ _ _ (le_refl _)
        (fun post kept => ⟨kept.1,kept.2.trans facts.2⟩) tailRun)
  simpa only [Nat.zero_add] using combined

#print axioms validate_headers_first_phase_reaches
end InitECandidate.Runtime
