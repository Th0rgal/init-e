import InitECandidate.Runtime.HashDeleteLinkedLoopStepSupported
import InitECandidate.Runtime.HashDeleteLoopRankedExitSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The complete original deletion scan preserves order linkage for its final
hole and consumes at most 55 clocks per table slot. -/
theorem evaluate_hashDelete_linked_loop_capacity_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      HashDeleteLinkedLoopExitWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock := by
  have bounds := valid.base.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,exitValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_exit_supported
    (HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits)
    (HashDeleteLinkedLoopExitWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits)
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.base.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => currentValid.dec_clock keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits current)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => currentValid.step_supported keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits current supported ticks)
    state valid (Nat.le_trans (Nat.mul_le_mul_right 55 bounds.2) budget)
  exact ⟨post,run,exitValid,by have := Nat.mul_le_mul_right 55 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_linked_loop_capacity_supported
end InitECandidate.Runtime
