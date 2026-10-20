import InitECandidate.Runtime.SourceCostLoopLiveBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- A reached suffix receives the exact locals projection proved by the
costed prefix. Their executed work composes additively. -/
theorem loop_live_paid_seq_next {F : Type} {s middle : LoopSemStateFiniteExact 64 F}
    {first second : HolLoopProg 64} {output} {a b : Nat}
    (one : LoopLivePaid s first (none, middle) a)
    (two : LoopLivePaid middle second output b) :
    LoopLivePaid s (.seq first second) output (a + b) := by
  intro contexts locals live input
  rcases compiledSecond : shrinkHOL contexts second live with ⟨second', middleLive⟩
  have firstInput : sptSubspt (sptInter s.locals (shrinkHOL contexts first middleLive).2) locals := by
    simpa only [shrinkHOL, compiledSecond] using input
  obtain ⟨middleLocals, a', firstRun, firstBound, middleRelated⟩ :=
    one contexts locals middleLive firstInput
  have secondInput :
      sptSubspt (sptInter middle.locals (shrinkHOL contexts second live).2) middleLocals := by
    rw [compiledSecond]
    exact middleRelated
  obtain ⟨postLocals, b', secondRun, secondBound, postRelated⟩ :=
    two contexts middleLocals live secondInput
  refine ⟨postLocals, a' + b', ?_, by omega, postRelated⟩
  simpa only [shrinkHOL, compiledSecond] using LoopWork.seqNext firstRun secondRun

/-- A terminal prefix never charges or executes the dead sequence suffix. -/
theorem loop_live_paid_seq_stop {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {first second : HolLoopProg 64} {result : LoopResultExact 64} {a : Nat}
    (one : LoopLivePaid s first (some result, post) a) :
    LoopLivePaid s (.seq first second) (some result, post) a := by
  intro contexts locals live input
  rcases compiledSecond : shrinkHOL contexts second live with ⟨second', middleLive⟩
  have firstInput : sptSubspt (sptInter s.locals (shrinkHOL contexts first middleLive).2) locals := by
    simpa only [shrinkHOL, compiledSecond] using input
  obtain ⟨postLocals, a', firstRun, bound, related⟩ := one contexts locals middleLive firstInput
  refine ⟨postLocals, a', ?_, bound, ?_⟩
  · simpa only [shrinkHOL, compiledSecond] using
      (LoopWork.seqStop (second := second') firstRun)
  · cases result <;> exact related

/-- Liveness removes Mark without adding work or changing the relation. -/
theorem loop_live_paid_mark {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output} {w : Nat} (inner : LoopLivePaid s p output w) :
    LoopLivePaid s (.mark p) output w := by
  intro contexts locals live input
  simpa only [shrinkHOL] using inner contexts locals live (by simpa only [shrinkHOL] using input)

#print axioms loop_live_paid_seq_next
#print axioms loop_live_paid_seq_stop
#print axioms loop_live_paid_mark
end InitECandidate.Runtime.FineCost
