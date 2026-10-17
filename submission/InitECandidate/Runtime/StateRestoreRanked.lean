import InitECandidate.Runtime.StateRestoreIterationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Rank induction for the actual rollback loop. The state invariant must
justify the original guard and preserve the remaining-record rank. -/
theorem evaluate_stateRestore_ranked {F : Type}
    (invariant : PanSemStateFiniteExact 64 F → Prop)
    (rank : PanSemStateFiniteExact 64 F → Nat) (cost : Nat)
    (guard : ∀ state, invariant state → evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) stateRestoreCondition =
      some (.val (.word (if rank state = 0 then 0 else 1))))
    (entryInvariant : ∀ state, invariant state → invariant (decClockHOLFinite state))
    (entryRank : ∀ state, rank (decClockHOLFinite state) = rank state)
    (step : ∀ state, invariant state → 0 < rank state → cost ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state stateRestoreLoopBody = (none,post) ∧
        invariant post ∧ rank post < rank state ∧ state.clock ≤ post.clock + cost ∧
        post.clock ≤ state.clock) :
    ∀ state, invariant state → rank state * (cost + 1) ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (none,post) ∧
        invariant post ∧ rank post = 0 ∧ state.clock ≤ post.clock + rank state * (cost + 1) ∧
        post.clock ≤ state.clock := by
  classical
  have visit : ∀ n : Nat, ∀ state, invariant state → rank state = n → n * (cost + 1) ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (none,post) ∧
        invariant post ∧ rank post = 0 ∧ state.clock ≤ post.clock + n * (cost + 1) ∧
        post.clock ≤ state.clock := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro state valid distance budget
      by_cases zero : n = 0
      · refine ⟨state,?_,valid,by omega,by omega,by omega⟩
        rw [evaluateHOLFiniteState_while_total,guard state valid]
        simp [distance,zero]
      · have positive : 0 < rank state := by omega
        let entry := decClockHOLFinite state
        have entryClock : entry.clock = state.clock - 1 := rfl
        have allocation : cost + 1 ≤ n * (cost + 1) := by
          have h := Nat.mul_le_mul_right (cost + 1) (show 1 ≤ n by omega)
          simpa using h
        have nonzero : state.clock ≠ 0 := by omega
        obtain ⟨next,body,nextValid,decrease,bodyCost,remaining⟩ :=
          step entry (entryInvariant state valid) (by rw [entryRank]; exact positive) (by omega)
        have smaller : rank next < n := by rw [entryRank state,distance] at decrease; exact decrease
        have reserve : (rank next + 1) * (cost + 1) ≤ n * (cost + 1) :=
          Nat.mul_le_mul_right (cost + 1) (by omega)
        rw [Nat.add_mul] at reserve
        have nextBudget : rank next * (cost + 1) ≤ next.clock := by omega
        obtain ⟨post,tail,postValid,done,tailCost,tailRemaining⟩ :=
          ih (rank next) smaller next nextValid rfl nextBudget
        have run : evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) =
            evaluateHOLFiniteState next (.while stateRestoreCondition stateRestoreLoopBody) := by
          rw [evaluateHOLFiniteState_while_total,guard state valid]
          simp [distance,zero,nonzero,body,fixClockHOLFinite,show ¬entry.clock < next.clock by omega,entry]
        exact ⟨post,run.trans tail,postValid,done,by omega,by omega⟩
  intro state valid budget
  exact visit (rank state) state valid rfl budget

#print axioms evaluate_stateRestore_ranked
end InitECandidate.Runtime
