import InitECandidate.Runtime.SourceCostLoopLiveGeometryG
import Flapjack.Pancake.LoopLive.Fixedpoint
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- Exact compiler metadata shared by all actual iterations of this loop.
These are liveness/compilation equations, not assumed runtime bounds. -/
structure LoopLivePlan (contexts : List (NumSet × NumSet)) (liveIn liveOut : NumSet)
    (body : HolLoopProg 64) (wanted : NumSet) where
  header : NumSet
  bodyCode : HolLoopProg 64
  bodyLive : NumSet
  breakLive : NumSet
  compiled : shrinkHOL contexts (.loop liveIn body liveOut) wanted =
    (.loop header bodyCode (sptInter liveOut wanted), header)
  bodyCompiled : shrinkHOL ((header, breakLive) :: contexts) body
    (sptUnion liveIn (sptInter liveOut wanted)) = (bodyCode, bodyLive)
  headerInside : ∀ key, sptMem key header → sptMem key liveIn
  bodyNeeds : ∀ key, sptMem key bodyLive → sptMem key liveIn → sptMem key header
  breakNeeds : ∀ key, sptMem key (sptInter liveOut wanted) → sptMem key breakLive

/-- Both actual fixed-point outcomes supply the plan, using the pinned
fixedpoint theorem. No invariant on a guessed compiled loop is assumed. -/
theorem loop_live_planG (contexts : List (NumSet × NumSet)) (liveIn liveOut : NumSet)
    (body : HolLoopProg 64) (wanted : NumSet) :
    Nonempty (LoopLivePlan contexts liveIn liveOut body wanted) := by
  cases fixed : fixedpointHOL contexts liveIn .ln (sptUnion liveIn (sptInter liveOut wanted)) body with
  | some pair =>
    rcases pair with ⟨bodyCode, bodyLive⟩
    refine ⟨⟨sptInter liveIn bodyLive, bodyCode, bodyLive,
      sptUnion liveIn (sptInter liveOut wanted), ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [shrinkHOL]
      simp only [fixed]
    · exact fixedpoint_thm contexts liveIn .ln _ body bodyLive bodyCode fixed
    · intro key member
      exact ((live_mem_interG liveIn bodyLive key).mp member).1
    · intro key needed inside
      exact (live_mem_interG liveIn bodyLive key).mpr ⟨inside, needed⟩
    · intro key member
      exact (sptMem_sptUnion _ _ key).mpr (Or.inr member)
  | none =>
    rcases compiledBody : shrinkHOL ((liveIn, sptInter liveOut wanted) :: contexts) body
        (sptUnion liveIn (sptInter liveOut wanted)) with ⟨bodyCode, bodyLive⟩
    refine ⟨⟨liveIn, bodyCode, bodyLive, sptInter liveOut wanted, ?_, compiledBody,
      fun _ member => member, fun _ _ inside => inside, fun _ member => member⟩⟩
    rw [shrinkHOL]
    simp only [fixed, compiledBody]

#print axioms loop_live_planG
end InitECandidate.Runtime.FineCost
