import InitECandidate.Runtime.SourceCostLoopLiveLeafG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- The quantitative induction conclusion uses the ORIGINAL liveness input
projection and result-indexed successor relation. -/
def LoopLivePaidG (L : LeafPrice) {F : Type} (s : LoopSemStateFiniteExact 64 F) (p : HolLoopProg 64)
    (output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) (w : Nat) : Prop :=
  ∀ (contexts : List (NumSet × NumSet)) (locals : Spt (WordLocW 64)) (live : NumSet),
    sptSubspt (sptInter s.locals (shrinkHOL contexts p live).2) locals →
      ∃ targetLocals w', LoopWorkG L { s with locals := locals } (shrinkHOL contexts p live).1
          (output.1, { output.2 with locals := targetLocals }) w' ∧ w' ≤ w ∧
        liveLocalsAfterG contexts live output.1 output.2.locals targetLocals

/-- Existing semantic correctness identifies the successor of an independently
constructed costed target trace. It supplies NO quantitative work bound. -/
theorem loop_live_finishG {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {result : Option (LoopResultExact 64)} {w : Nat}
    (source : LoopWorkG L s p (result, post) w) (nonerror : result ≠ some .error)
    (contexts : List (NumSet × NumSet)) (locals : Spt (WordLocW 64)) (live : NumSet)
    (input : sptSubspt (sptInter s.locals (shrinkHOL contexts p live).2) locals)
    {targetOutput : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F} {w' : Nat}
    (target : LoopWorkG L { s with locals := locals } (shrinkHOL contexts p live).1 targetOutput w')
    (bound : w' ≤ w) :
    ∃ targetLocals cost, LoopWorkG L { s with locals := locals } (shrinkHOL contexts p live).1
        (result, { post with locals := targetLocals }) cost ∧ cost ≤ w ∧
      liveLocalsAfterG contexts live result post.locals targetLocals := by
  obtain ⟨targetLocals, evaluated, related⟩ := loopLive_compile_correct p s result post contexts
    locals (shrinkHOL contexts p live).1 (shrinkHOL contexts p live).2 live
      ⟨source.sound, nonerror, rfl, input⟩
  have same := target.sound.symm.trans evaluated
  rw [same] at target
  refine ⟨targetLocals, w', target, bound, ?_⟩
  cases result with
  | none => exact related
  | some result => cases result <;> exact related

theorem loop_live_paid_leafG {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {result : Option (LoopResultExact 64)} {w : Nat}
    (source : LoopWorkG L s p (result, post) w) (leaf : L.lf p = some w)
    (nonerror : result ≠ some .error) : LoopLivePaidG L s p (result, post) w :=
  fun contexts locals live input => loop_live_leaf_workG source leaf nonerror contexts locals live input

#print axioms loop_live_finishG
#print axioms loop_live_paid_leafG
end InitECandidate.Runtime.FineCost
