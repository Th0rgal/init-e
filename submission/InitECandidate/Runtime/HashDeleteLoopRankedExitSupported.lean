import InitECandidate.Runtime.HashDeleteLoopRanked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Rank induction with a separate break postcondition. Continuing iterations
retain the pre-body invariant; the final empty-slot iteration may discharge it. -/
theorem evaluate_hashDelete_loop_ranked_exit_supported {F : Type}
    (invariant exitCondition : PanSemStateFiniteExact 64 F → Prop)
    (rank : PanSemStateFiniteExact 64 F → Nat)
    (positive : ∀ state, invariant state → 0 < rank state)
    (entryInvariant : ∀ state, invariant state → invariant (decClockHOLFinite state))
    (entryRank : ∀ state, rank (decClockHOLFinite state) = rank state)
    (step : ∀ state, invariant state → 54 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 54 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) ∧ exitCondition post) ∨
         (evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) ∧ invariant post ∧ rank post < rank state))) :
    ∀ state, invariant state → rank state * 55 ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧ exitCondition post ∧
        state.clock ≤ post.clock + rank state * 55 ∧ post.clock ≤ state.clock := by
  classical
  have visit : ∀ n : Nat, ∀ state, invariant state → rank state = n → n * 55 ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧ exitCondition post ∧
        state.clock ≤ post.clock + n * 55 ∧ post.clock ≤ state.clock := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro state valid distance budget
      have nonzero : state.clock ≠ 0 := by have := positive state valid; omega
      let entry := decClockHOLFinite state
      have entryClock : entry.clock = state.clock - 1 := rfl
      have entryBound : 54 ≤ entry.clock := by have := positive state valid; omega
      obtain ⟨next,cost,remaining,body⟩ := step entry (entryInvariant state valid) entryBound
      rcases body with stopped | running
      · obtain ⟨stopped,exitValid⟩ := stopped
        have run : evaluateHOLFiniteState state hashDeleteLoop = (none,next) := by
          unfold hashDeleteLoop
          rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact]
          simp [evalHOLExact,nonzero,stopped,fixClockHOLFinite,show ¬entry.clock < next.clock by omega,entry]
        exact ⟨next,run,exitValid,by have := positive state valid; omega,by omega⟩
      · obtain ⟨bodyRun,nextValid,decrease⟩ := running
        have smaller : rank next < n := by rw [entryRank state,distance] at decrease; exact decrease
        have allocation : (rank next + 1) * 55 ≤ n * 55 := Nat.mul_le_mul_right 55 (by omega)
        rw [Nat.add_mul] at allocation
        have nextBudget : rank next * 55 ≤ next.clock := by omega
        obtain ⟨post,tail,postValid,tailCost,tailRemaining⟩ := ih (rank next) smaller next nextValid rfl nextBudget
        have run : evaluateHOLFiniteState state hashDeleteLoop = evaluateHOLFiniteState next hashDeleteLoop := by
          unfold hashDeleteLoop
          rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact]
          simp [evalHOLExact,nonzero,bodyRun,fixClockHOLFinite,show ¬entry.clock < next.clock by omega,entry]
        exact ⟨post,run.trans tail,postValid,by omega,by omega⟩
  intro state valid budget
  exact visit (rank state) state valid rfl budget

#print axioms evaluate_hashDelete_loop_ranked_exit_supported
end InitECandidate.Runtime
