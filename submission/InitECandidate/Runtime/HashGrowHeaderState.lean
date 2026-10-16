import InitECandidate.Runtime.HashGrowHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Header installation changes only memory, expressed as a single state update. -/
theorem htabGrowHeaderPost_state {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos : BitVec 64) :
    htabGrowHeaderPost state table capacity keys values used order orderPos =
      {state with memory := (htabGrowHeaderPost state table capacity keys values used order orderPos).memory} := by
  simp only [htabGrowHeaderPost,sourceWriteWord]

#print axioms htabGrowHeaderPost_state
end InitECandidate.Runtime
