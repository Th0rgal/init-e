import InitECandidate.Runtime.RankedLoopReturnsInvariant
/-!
Rank induction for source `while` loops whose early exits satisfy a stated predicate `Q` (root's
`evaluate_ranked_loop_returns_invariant` with the exit outcome reported).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem evaluate_ranked_loop_returnsQ {F : Type}
    (condition : ExpHOL 64) (loopBody : ProgHOL 64)
    (invariant : PanSemStateFiniteExact 64 F → Prop)
    (rank : PanSemStateFiniteExact 64 F → Nat) (cost : Nat)
    (Q : PanSemResultExact 64 → PanSemStateFiniteExact 64 F → Prop)
    (guard : ∀ state, invariant state → evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) condition =
      some (.val (.word (if rank state = 0 then 0 else 1))))
    (entryInvariant : ∀ state, invariant state → invariant (decClockHOLFinite state))
    (entryRank : ∀ state, rank (decClockHOLFinite state) = rank state)
    (step : ∀ state, invariant state → 0 < rank state → cost ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + cost ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state loopBody = (none,post) ∧ invariant post ∧ rank post < rank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ Q result post ∧
           evaluateHOLFiniteState state loopBody = (some result,post)))) :
    ∀ state, invariant state → rank state * (cost + 1) ≤ state.clock →
      ∃ result post, evaluateHOLFiniteState state (.while condition loopBody) = (result,post) ∧ state.clock ≤ post.clock + rank state * (cost + 1) ∧
        post.clock ≤ state.clock ∧ ((result = none ∧ invariant post ∧ rank post = 0) ∨ ∃ r, result = some r ∧ Q r post) := by
  classical
  have visit : ∀ n : Nat, ∀ state, invariant state → rank state = n → n * (cost + 1) ≤ state.clock →
      ∃ result post, evaluateHOLFiniteState state (.while condition loopBody) = (result,post) ∧ state.clock ≤ post.clock + n * (cost + 1) ∧
        post.clock ≤ state.clock ∧ ((result = none ∧ invariant post ∧ rank post = 0) ∨ ∃ r, result = some r ∧ Q r post) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro state valid distance budget
      by_cases zero : n = 0
      · refine ⟨none,state,?_,by omega,by omega,Or.inl ⟨rfl,valid,by omega⟩⟩
        rw [evaluateHOLFiniteState_while_total,guard state valid]
        simp [distance,zero]
      · have positive : 0 < rank state := by omega
        let entry := decClockHOLFinite state
        have entryClock : entry.clock = state.clock - 1 := rfl
        have allocation : cost + 1 ≤ n * (cost + 1) := by
          have h := Nat.mul_le_mul_right (cost + 1) (show 1 ≤ n by omega)
          simpa using h
        have nonzero : state.clock ≠ 0 := by omega
        obtain ⟨next,bodyCost,remaining,bodyCases⟩ :=
          step entry (entryInvariant state valid) (by rw [entryRank]; exact positive) (by omega)
        rcases bodyCases with running | stopped
        · obtain ⟨body,nextValid,decrease⟩ := running
          have smaller : rank next < n := by rw [entryRank state,distance] at decrease; exact decrease
          have reserve : (rank next + 1) * (cost + 1) ≤ n * (cost + 1) :=
            Nat.mul_le_mul_right (cost + 1) (by omega)
          rw [Nat.add_mul] at reserve
          have nextBudget : rank next * (cost + 1) ≤ next.clock := by omega
          obtain ⟨result,post,tail,tailCost,tailRemaining,tailOut⟩ :=
            ih (rank next) smaller next nextValid rfl nextBudget
          have run : evaluateHOLFiniteState state (.while condition loopBody) =
              evaluateHOLFiniteState next (.while condition loopBody) := by
            rw [evaluateHOLFiniteState_while_total,guard state valid]
            simp [distance,zero,nonzero,body,fixClockHOLFinite,show ¬entry.clock < next.clock by omega,entry]
          exact ⟨result,post,run.trans tail,by omega,by omega,tailOut⟩
        · obtain ⟨result,notContinue,notTimeout,notBreak,q,body⟩ := stopped
          have fixed : ¬entry.clock < next.clock := by omega
          refine ⟨some result,next,?_,by omega,by omega,Or.inr ⟨result,rfl,q⟩⟩
          rw [evaluateHOLFiniteState_while_total,guard state valid]
          cases result <;> simp [distance,zero,nonzero,body,fixClockHOLFinite,fixed,entry] at *
  intro state valid budget
  exact visit (rank state) state valid rfl budget


#print axioms evaluate_ranked_loop_returnsQ
end InitECandidate.Runtime
