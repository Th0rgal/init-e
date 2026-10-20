import InitECandidate.Runtime.SourceCostLoopLiveLeaf
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- The quantitative induction conclusion uses the ORIGINAL liveness input
projection and result-indexed successor relation. -/
def LoopLivePaid {F : Type} (s : LoopSemStateFiniteExact 64 F) (p : HolLoopProg 64)
    (output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) (w : Nat) : Prop :=
  ∀ (contexts : List (NumSet × NumSet)) (locals : Spt (WordLocW 64)) (live : NumSet),
    sptSubspt (sptInter s.locals (shrinkHOL contexts p live).2) locals →
      ∃ targetLocals w', LoopWork { s with locals := locals } (shrinkHOL contexts p live).1
          (output.1, { output.2 with locals := targetLocals }) w' ∧ w' ≤ w ∧
        liveLocalsAfter contexts live output.1 output.2.locals targetLocals

/-- Existing semantic correctness identifies the successor of an independently
constructed costed target trace. It supplies NO quantitative work bound. -/
theorem loop_live_finish {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {result : Option (LoopResultExact 64)} {w : Nat}
    (source : LoopWork s p (result, post) w) (nonerror : result ≠ some .error)
    (contexts : List (NumSet × NumSet)) (locals : Spt (WordLocW 64)) (live : NumSet)
    (input : sptSubspt (sptInter s.locals (shrinkHOL contexts p live).2) locals)
    {targetOutput : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w' : Nat}
    (target : LoopWork { s with locals := locals } (shrinkHOL contexts p live).1 targetOutput w')
    (bound : w' ≤ w) :
    ∃ targetLocals cost, LoopWork { s with locals := locals } (shrinkHOL contexts p live).1
        (result, { post with locals := targetLocals }) cost ∧ cost ≤ w ∧
      liveLocalsAfter contexts live result post.locals targetLocals := by
  obtain ⟨targetLocals, evaluated, related⟩ := loopLive_compile_correct p s result post contexts
    locals (shrinkHOL contexts p live).1 (shrinkHOL contexts p live).2 live
      ⟨source.sound, nonerror, rfl, input⟩
  have same := target.sound.symm.trans evaluated
  rw [same] at target
  refine ⟨targetLocals, w', target, bound, ?_⟩
  cases result with
  | none => exact related
  | some result => cases result <;> exact related

theorem loop_live_paid_leaf {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {result : Option (LoopResultExact 64)} {w : Nat}
    (source : LoopWork s p (result, post) w) (leaf : loopWorkLeafCost p = some w)
    (nonerror : result ≠ some .error) : LoopLivePaid s p (result, post) w :=
  fun contexts locals live input => loop_live_leaf_work source leaf nonerror contexts locals live input

#print axioms loop_live_finish
#print axioms loop_live_paid_leaf
end InitECandidate.Runtime.FineCost
