import InitECandidate.Runtime.WordExecutionCostProps
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000

/-- Every reached node pays its own configured local price, including
malformed/error paths and calls that stop before entering the callee. -/
theorem wordExecutionCost_local_le {width : Nat} [NeZero width] {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (p : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    price p source ≤ wordExecutionCost price p source := by
  cases p <;> rw [wordExecutionCost]
  all_goals repeat' first | omega | (solve | simp) | split
  all_goals dsimp only; omega

#print axioms wordExecutionCost_local_le
end InitECandidate.Runtime.FineCost
