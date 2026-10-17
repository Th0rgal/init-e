import InitECandidate.Runtime.HashDeleteLinkedLoopStep32
import InitECandidate.Runtime.HashDeleteLoopRankedExit
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The complete original deletion scan preserves order linkage for its final
hole and consumes at most 35 clocks per table slot. -/
theorem evaluate_hashDelete_linked_loop_capacity32 {F : Type}
    (table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      HashDeleteLinkedLoopExit32 table keys stride capacity used values order orderPos items empty deletedPosition bits post ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock := by
  have bounds := valid.base.rank_bounds table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,exitValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_exit
    (HashDeleteLinkedLoopInvariant32 table keys stride capacity used values order orderPos items empty deletedPosition bits)
    (HashDeleteLinkedLoopExit32 table keys stride capacity used values order orderPos items empty deletedPosition bits)
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.base.rank_bounds table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => currentValid.dec_clock table keys stride capacity used values order orderPos items empty deletedPosition bits current)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => currentValid.step table keys stride capacity used values order orderPos items empty deletedPosition bits current ticks)
    state valid (Nat.le_trans (Nat.mul_le_mul_right 35 bounds.2) budget)
  exact ⟨post,run,exitValid,by have := Nat.mul_le_mul_right 35 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_linked_loop_capacity32
end InitECandidate.Runtime
