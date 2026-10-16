import InitECandidate.Runtime.CrepOptimizedCeiling
namespace InitECandidate.Runtime
open Flapjack

/-- A numerical size ceiling extracted from the actual finite code-map support.
This works for every exact code map without an external size certificate. -/
noncomputable def crepFiniteCodeLimit {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) : Nat :=
  ((Classical.choose code.finiteSupport).map (fun key =>
    match code.lookup key with | none => 0 | some (_,body) => sizeOf body)).sum

private theorem mapped_sum_bound {α : Type} (keys : List α) (f : α → Nat)
    (key : α) (member : key ∈ keys) : f key ≤ (keys.map f).sum := by
  induction keys with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [List.map_cons,List.sum_cons]
    rcases member with equal | member
    · subst key; omega
    · have := ih member; omega

theorem crep_finite_code_bounded {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) : CrepCodeSize (crepFiniteCodeLimit s.code) s := by
  intro name params body found
  have member := Classical.choose_spec s.code.finiteSupport name (by rw [found]; simp)
  have bound := mapped_sum_bound (Classical.choose s.code.finiteSupport)
    (fun key => match s.code.lookup key with | none => 0 | some (_,body) => sizeOf body) name member
  simpa only [found,crepFiniteCodeLimit] using bound

/-- Unconditional numerical compiler ceiling for any finite exact Crep code
map; the current program size is included in the extracted procedure limit. -/
theorem crep_finite_uniform_ceiling {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt p s
      (workCeiling (max (sizeOf p) (crepFiniteCodeLimit s.code)) s.clock (sizeOf p)) := by
  apply crep_uniform_ceiling _ p s (Nat.le_max_left _ _)
  intro name params body found
  exact Nat.le_trans (crep_finite_code_bounded s name params body found) (Nat.le_max_right _ _)

#print axioms crep_finite_code_bounded
#print axioms crep_finite_uniform_ceiling
end InitECandidate.Runtime
