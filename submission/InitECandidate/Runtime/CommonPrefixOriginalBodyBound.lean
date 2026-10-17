import InitECandidate.Runtime.CommonPrefixBodyBound
import InitECandidate.Runtime.OriginalMinCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_original_commonPrefix_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : BitVec 64)
    (leftLocal : state.locals.lookup (ofString "al") = some (.val (.word left)))
    (rightLocal : state.locals.lookup (ofString "bl") = some (.val (.word right)))
    (code : state.code = originalRuntimeCode)
    (ticks : (wordMin left right).toNat + 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_common_prefix_length) = (result,post) ∧
      state.clock ≤ post.clock + (wordMin left right).toNat + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ found : BitVec 64,
        value = .val (.word found) ∧ found.toNat ≤ left.toNat ∧ found.toNat ≤ right.toNat) := by
  have installed : state.code.lookup (ofString "min") = some minCodeEntry := by
    rw [code]
    exact originalRuntimeCode_min_lookup
  exact evaluate_commonPrefix_body_bounded state left right leftLocal rightLocal installed ticks

#print axioms evaluate_original_commonPrefix_body_bounded
end InitECandidate.Runtime
