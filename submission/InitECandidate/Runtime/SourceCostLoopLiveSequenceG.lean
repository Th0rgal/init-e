import InitECandidate.Runtime.SourceCostLoopLiveBaseG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- A reached suffix receives the exact locals projection proved by the
costed prefix. Their executed work composes additively. -/
theorem loop_live_paid_seq_nextG {F : Type} {s middle : LoopSemStateFiniteExact 64 F}
    {first second : HolLoopProg 64} {output} {a b : Nat}
    (one : LoopLivePaidG L s first (none, middle) a)
    (two : LoopLivePaidG L middle second output b) :
    LoopLivePaidG L s (.seq first second) output (a + b) := by
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
  simpa only [shrinkHOL, compiledSecond] using LoopWorkG.seqNext firstRun secondRun

/-- A terminal prefix never charges or executes the dead sequence suffix. -/
theorem loop_live_paid_seq_stopG {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {first second : HolLoopProg 64} {result : LoopResultExact 64} {a : Nat}
    (one : LoopLivePaidG L s first (some result, post) a) :
    LoopLivePaidG L s (.seq first second) (some result, post) a := by
  intro contexts locals live input
  rcases compiledSecond : shrinkHOL contexts second live with ⟨second', middleLive⟩
  have firstInput : sptSubspt (sptInter s.locals (shrinkHOL contexts first middleLive).2) locals := by
    simpa only [shrinkHOL, compiledSecond] using input
  obtain ⟨postLocals, a', firstRun, bound, related⟩ := one contexts locals middleLive firstInput
  refine ⟨postLocals, a', ?_, bound, ?_⟩
  · simpa only [shrinkHOL, compiledSecond] using
      (LoopWorkG.seqStop (second := second') firstRun)
  · cases result <;> exact related

/-- Liveness removes Mark without adding work or changing the relation. -/
theorem loop_live_paid_markG {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output} {w : Nat} (inner : LoopLivePaidG L s p output w) :
    LoopLivePaidG L s (.mark p) output w := by
  intro contexts locals live input
  simpa only [shrinkHOL] using inner contexts locals live (by simpa only [shrinkHOL] using input)

#print axioms loop_live_paid_seq_nextG
#print axioms loop_live_paid_seq_stopG
#print axioms loop_live_paid_markG
end InitECandidate.Runtime.FineCost
