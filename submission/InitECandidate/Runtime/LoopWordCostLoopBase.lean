import InitECandidate.Runtime.LoopWordCostBase
import Flapjack.Pancake.Proofs.LoopToWord.TickUnfold
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Word-side unfolding of a compiled Loop `loop`: `Tick; loop; Tick`. -/

section
variable {C F : Type}

theorem tick_loop_tick_zero (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (zero : t.clock = 0) :
    wordExecutionCost loopWordPrice (.seq .tick (.seq (.loop names body exitNames) .tick)) t = 1 := by
  rw [wordExecutionCost_seq, evaluate_tick_unfold, if_pos zero, wordCost_tick]
  simp [loopWordPrice]

theorem tick_loop_tick_upper (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (nz : t.clock ≠ 0) :
    wordExecutionCost loopWordPrice (.seq .tick (.seq (.loop names body exitNames) .tick)) t ≤
      2 + wordExecutionCost loopWordPrice (.loop names body exitNames) (decClock t) := by
  rw [wordExecutionCost_seq, evaluate_tick_unfold, if_neg nz, wordCost_tick]
  simp only
  have := wordCost_seq_le loopWordPrice (decClock t) (.loop names body exitNames) .tick 1
    (fun m => by rw [wordCost_tick]; simp [loopWordPrice])
  simp only [loopWordPrice] at this ⊢
  omega

theorem tick_loop_tick_lower (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (nz : t.clock ≠ 0) :
    1 + wordExecutionCost loopWordPrice (.loop names body exitNames) (decClock t) ≤
      wordExecutionCost loopWordPrice (.seq .tick (.seq (.loop names body exitNames) .tick)) t := by
  rw [wordExecutionCost_seq, evaluate_tick_unfold, if_neg nz, wordCost_tick]
  simp only
  rw [wordExecutionCost_seq]
  simp only [loopWordPrice]
  omega

/-- One Word loop iteration from a successful cut. -/
theorem loop_iteration_cost (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (u entry : WordSemStateFiniteExact 64 C F) (cut : cutState (names, .ln) u = some entry)
    {res1 t1} (run : evaluate body entry = (res1, t1)) :
    wordExecutionCost loopWordPrice (.loop names body exitNames) u =
      1 + wordExecutionCost loopWordPrice body entry +
        (if wordSemContLoop res1 then
          (if t1.clock = 0 then 0 else wordExecutionCost loopWordPrice (.loop names body exitNames) (decClock t1))
         else 0) := by
  rw [wordExecutionCost]
  split
  · rename_i h; rw [cut] at h; cases h
  · rename_i e h
    rw [cut] at h
    cases h
    split
    rename_i r m hm
    rw [fix_clock_evaluate, run] at hm
    cases hm
    simp only [loopWordPrice, wordSemSTOP]
    by_cases hc : wordSemContLoop res1 = true
    · simp only [hc, ↓reduceIte]
      by_cases hz : t1.clock = 0
      · simp [hz]
      · simp [hz]
    · simp [hc]
end

#print axioms tick_loop_tick_zero
#print axioms tick_loop_tick_upper
#print axioms tick_loop_tick_lower
#print axioms loop_iteration_cost
end InitECandidate.Runtime.FineCost
