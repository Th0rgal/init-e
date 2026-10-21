import InitECandidate.Runtime.SourceCostLoopMarkG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice}

/-- Pruning an atomic statement keeps it or drops it to `skip`. -/
theorem shrink_leaf_cases (p : HolLoopProg 64) (contexts : List (NumSet × NumSet)) (live : NumSet)
    (leaf : (loopWorkLeafCost p).isSome = true) :
    (shrinkHOL contexts p live).1 = p ∨ (shrinkHOL contexts p live).1 = .skip ∨
      ∃ f a b c d l l', p = .ffi f a b c d l ∧ (shrinkHOL contexts p live).1 = .ffi f a b c d l' := by
  cases p <;> simp [loopWorkLeafCost] at leaf
  all_goals simp only [shrinkHOL]
  all_goals try split
  all_goals simp

/-- Pruning an atomic statement retains it or drops a dead assignment/label
value to Skip. Its local work cannot increase. -/
theorem loop_live_leaf_costG (p : HolLoopProg 64) (cost : Nat)
    (contexts : List (NumSet × NumSet)) (live : NumSet)
    (leaf : L.lf p = some cost) :
    ∃ cost', L.lf (shrinkHOL contexts p live).1 = some cost' ∧ cost' ≤ cost := by
  rcases shrink_leaf_cases p contexts live (L.dom _ _ leaf) with h | h | ⟨f, a, b, c, d, l, l', rfl, h⟩
  · exact ⟨cost, by rw [h]; exact leaf, Nat.le_refl _⟩
  · exact ⟨0, by rw [h]; exact L.skip, Nat.zero_le _⟩
  · exact ⟨cost, by rw [h, L.ffiLive f a b c d l' l]; exact leaf, Nat.le_refl _⟩

/-- The original liveness theorem's successor-local relation, factored so
compositional cost proofs can reuse its semantics without repeating leaves. -/
def liveLocalsAfterG (contexts : List (NumSet × NumSet)) (live : NumSet)
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
theorem loop_live_leaf_workG {F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {result : Option (LoopResultExact 64)} {cost : Nat}
    (run : LoopWorkG L s p (result, post) cost) (leaf : L.lf p = some cost)
    (nonerror : result ≠ some .error) (contexts : List (NumSet × NumSet))
    (locals : Spt (WordLocW 64)) (live : NumSet)
    (input : sptSubspt (sptInter s.locals (shrinkHOL contexts p live).2) locals) :
    ∃ targetLocals cost', LoopWorkG L { s with locals := locals } (shrinkHOL contexts p live).1
        (result, { post with locals := targetLocals }) cost' ∧ cost' ≤ cost ∧
      liveLocalsAfterG contexts live result post.locals targetLocals := by
  obtain ⟨targetLocals, evaluated, related⟩ := loopLive_compile_correct p s result post contexts
    locals (shrinkHOL contexts p live).1 (shrinkHOL contexts p live).2 live
      ⟨run.sound, nonerror, rfl, input⟩
  obtain ⟨cost', targetLeaf, bound⟩ := loop_live_leaf_costG p cost contexts live leaf
  refine ⟨targetLocals, cost', LoopWorkG.atom targetLeaf evaluated, bound, ?_⟩
  cases result with
  | none => exact related
  | some result => cases result <;> exact related

#print axioms loop_live_leaf_costG
#print axioms loop_live_leaf_workG
end InitECandidate.Runtime.FineCost
