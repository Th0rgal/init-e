import InitECandidate.Runtime.ProgressiveLoopBound
import InitECandidate.Runtime.ProgressiveSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def progressiveLoopsCost : Nat := 134217712 * (merkleBodyCost + 2) + (16 + (progressiveFoldCost + 17))

/-- The actual two loops and final original suffix, including every early
memory failure or external outcome, have a uniform input-bounded cost. -/
theorem runBounded_progressive_loops {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64)
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode)
    (valid : ProgressiveRank p n roots heap state n.toNat)
    (budget : progressiveLoopsCost ≤ state.clock) :
    RunBounded state (progressiveAt 6) progressiveLoopsCost := by
  rw [source_progressive_loop]
  have firstBudget : n.toNat * (merkleBodyCost + 2) ≤ state.clock := by
    have mono := Nat.mul_le_mul_right (merkleBodyCost + 2) small
    unfold progressiveLoopsCost at budget
    omega
  have loopBound := runBounded_progressive_loop state p n roots heap n.toNat small heapBound code valid firstBudget
  have combined := RunBounded.seq (a := n.toNat * (merkleBodyCost + 2))
      (b := 16 + (progressiveFoldCost + 17)) loopBound (by
        have mono := Nat.mul_le_mul_right (merkleBodyCost + 2) small
        unfold progressiveLoopsCost at budget
        omega) (by
    intro next normal nextCode remaining
    obtain ⟨_,k,atK,kBound⟩ := progressive_loop_normal_k_bound state next p n roots heap n.toNat
      small heapBound code valid firstBudget normal
    exact runBounded_progressive_zero_suffix next k atK (by omega) (nextCode.trans code) remaining)
  exact combined.weaken (by
    have mono := Nat.mul_le_mul_right (merkleBodyCost + 2) small
    unfold progressiveLoopsCost
    omega)

#print axioms runBounded_progressive_loops
end InitECandidate.Runtime
