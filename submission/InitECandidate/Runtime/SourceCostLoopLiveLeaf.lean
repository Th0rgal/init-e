import InitECandidate.Runtime.SourceCostLoopMark
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- Pruning an atomic statement retains it or drops a dead assignment/label
value to Skip. Its local work cannot increase. -/
theorem loop_live_leaf_cost (p : HolLoopProg 64) (cost : Nat)
    (contexts : List (NumSet × NumSet)) (live : NumSet)
    (leaf : loopWorkLeafCost p = some cost) :
    ∃ cost', loopWorkLeafCost (shrinkHOL contexts p live).1 = some cost' ∧ cost' ≤ cost := by
  cases p <;> simp only [loopWorkLeafCost, Option.some.injEq, reduceCtorEq] at leaf
  all_goals try contradiction
  all_goals simp only [shrinkHOL]
  all_goals try split
  all_goals simp only [loopWorkLeafCost, Option.some.injEq]
  all_goals exact ⟨_, rfl, by omega⟩

/-- The original liveness theorem's successor-local relation, factored so
compositional cost proofs can reuse its semantics without repeating leaves. -/
def liveLocalsAfter (contexts : List (NumSet × NumSet)) (live : NumSet)
    (result : Option (LoopResultExact 64))
    (source target : Spt (WordLocW 64)) : Prop :=
  match result with
  | none => sptSubspt (sptInter source live) target
  | some (.break n) =>
      match sptOel n contexts with
      | some (_, exit) => sptSubspt (sptInter source exit) target
      | none => True
  | some (.continue n) =>
      match sptOel n contexts with
      | some (entry, _) => sptSubspt (sptInter source entry) target
      | none => True
  | _ => target = source

/-- Exact atomic liveness cost transfer under the ORIGINAL locals-projection
premise. Existing semantic correctness supplies the real successor and its
locals relation; the work proof uses only the checked local cost decrease. -/
theorem loop_live_leaf_work {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {result : Option (LoopResultExact 64)} {cost : Nat}
    (run : LoopWork s p (result, post) cost) (leaf : loopWorkLeafCost p = some cost)
    (nonerror : result ≠ some .error) (contexts : List (NumSet × NumSet))
    (locals : Spt (WordLocW 64)) (live : NumSet)
    (input : sptSubspt (sptInter s.locals (shrinkHOL contexts p live).2) locals) :
    ∃ targetLocals cost', LoopWork { s with locals := locals } (shrinkHOL contexts p live).1
        (result, { post with locals := targetLocals }) cost' ∧ cost' ≤ cost ∧
      liveLocalsAfter contexts live result post.locals targetLocals := by
  obtain ⟨targetLocals, evaluated, related⟩ := loopLive_compile_correct p s result post contexts
    locals (shrinkHOL contexts p live).1 (shrinkHOL contexts p live).2 live
      ⟨run.sound, nonerror, rfl, input⟩
  obtain ⟨cost', targetLeaf, bound⟩ := loop_live_leaf_cost p cost contexts live leaf
  refine ⟨targetLocals, cost', LoopWork.atom targetLeaf evaluated, bound, ?_⟩
  cases result with
  | none => exact related
  | some result => cases result <;> exact related

#print axioms loop_live_leaf_cost
#print axioms loop_live_leaf_work
end InitECandidate.Runtime.FineCost
