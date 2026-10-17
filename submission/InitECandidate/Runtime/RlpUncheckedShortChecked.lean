import InitECandidate.Runtime.RlpUncheckedShortValue
import InitECandidate.Runtime.RlpHeaderShortStringProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Success of the real checked short-string branch bounds the exact value
returned by the unchecked helper in the same input state. -/
theorem rlpUnchecked_short_string_checked_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderShortStringBranch = (some (.returned value),post)) :
    ∃ consumed : BitVec 64,
      evaluateHOLFiniteState state rlpUncheckedAfterByte =
        (some (.returned (.val (.word consumed))),emptyLocalsHOLFinite state) ∧
      0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  have checked := rlpHeader_short_string_scoped_progress state post header total value
    headerLocal totalLocal lower upper nonzero code run
  have equal : ((1 : BitVec 64) + header) - 128 = 1 + (header - 128) := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨(1 + header) - 128,?_,?_,?_⟩
  · simpa only [if_neg (show ¬header.toNat < 128 by omega)] using evaluate_rlpUnchecked_short_after_load state header headerLocal upper
  · rw [equal]; exact checked.2.1
  · rw [equal]; exact checked.2.2

#print axioms rlpUnchecked_short_string_checked_bound
end InitECandidate.Runtime
