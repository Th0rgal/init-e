import InitECandidate.Runtime.HeaderDecoderBodyBound
import Mathlib.Tactic.Ring
namespace InitECandidate.Runtime

/-- The complete original header-decoder source bound as an explicit polynomial. -/
theorem headerDecoderBodyCost_polynomial (limit : Nat) :
    headerDecoderBodyCost limit = 870 * limit * limit + 998 * limit + 2594677 := by
  simp only [headerDecoderBodyCost,decodeHeaderRlpCost,decodeHeaderSlicesCost,headerDecoderUnitCost,headerRlpFieldCost]
  ring

#print axioms headerDecoderBodyCost_polynomial
end InitECandidate.Runtime
