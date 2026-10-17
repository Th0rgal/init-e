import InitECandidate.Runtime.HashDeleteRank
import InitECandidate.Runtime.HashDeleteOccupiedIteration32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def hashDeleteLoop : ProgHOL 64 := .while (.const 1) hashDeleteLoopBody

/-- Rank induction for the original deletion loop. The body contract covers
its actual empty-slot break and occupied continuation, including copy costs. -/
theorem evaluate_hashDelete_loop_ranked {F : Type}
    (invariant : PanSemStateFiniteExact 64 F → Prop)
    (rank : PanSemStateFiniteExact 64 F → Nat)
    (positive : ∀ state, invariant state → 0 < rank state)
    (entryInvariant : ∀ state, invariant state → invariant (decClockHOLFinite state))
    (entryRank : ∀ state, rank (decClockHOLFinite state) = rank state)
    (step : ∀ state, invariant state → 34 ≤ state.clock →
      ∃ post, invariant post ∧ state.clock ≤ post.clock + 34 ∧ post.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) ∨
         (evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) ∧ rank post < rank state))) :
    ∀ state, invariant state → rank state * 35 ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧ invariant post ∧
        state.clock ≤ post.clock + rank state * 35 ∧ post.clock ≤ state.clock := by
  classical
  have visit : ∀ n : Nat, ∀ state, invariant state → rank state = n → n * 35 ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧ invariant post ∧
        state.clock ≤ post.clock + n * 35 ∧ post.clock ≤ state.clock := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro state valid distance budget
      have nonzero : state.clock ≠ 0 := by have := positive state valid; omega
      let entry := decClockHOLFinite state
      have entryClock : entry.clock = state.clock - 1 := rfl
      have entryBound : 34 ≤ entry.clock := by have := positive state valid; omega
      obtain ⟨next,nextValid,cost,remaining,body⟩ := step entry (entryInvariant state valid) entryBound
      rcases body with stopped | running
      · have run : evaluateHOLFiniteState state hashDeleteLoop = (none,next) := by
          unfold hashDeleteLoop
          rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact]
          simp [evalHOLExact,nonzero,stopped,fixClockHOLFinite,show ¬entry.clock < next.clock by omega,entry]
        exact ⟨next,run,nextValid,by have := positive state valid; omega,by omega⟩
      · obtain ⟨bodyRun,decrease⟩ := running
        have smaller : rank next < n := by rw [entryRank state,distance] at decrease; exact decrease
        have allocation : (rank next + 1) * 35 ≤ n * 35 := Nat.mul_le_mul_right 35 (by omega)
        rw [Nat.add_mul] at allocation
        have nextBudget : rank next * 35 ≤ next.clock := by omega
        obtain ⟨post,tail,postValid,tailCost,tailRemaining⟩ := ih (rank next) smaller next nextValid rfl nextBudget
        have run : evaluateHOLFiniteState state hashDeleteLoop = evaluateHOLFiniteState next hashDeleteLoop := by
          unfold hashDeleteLoop
          rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact]
          simp [evalHOLExact,nonzero,bodyRun,fixClockHOLFinite,show ¬entry.clock < next.clock by omega,entry]
        exact ⟨post,run.trans tail,postValid,by omega,by omega⟩
  intro state valid budget
  exact visit (rank state) state valid rfl budget

#print axioms evaluate_hashDelete_loop_ranked
end InitECandidate.Runtime
