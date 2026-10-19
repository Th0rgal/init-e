import InitECandidate.Runtime.MaximumReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real maximum return is bounded above by a common ceiling and below
by both inputs; Merkle padding starts no deeper than this returned target. -/
theorem max_body_returned_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (value : ValueHOL 64) (bound : Nat)
    (left : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (right : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (leftBound : a.toNat ≤ bound) (rightBound : b.toNat ≤ bound)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_max) = (some (.returned value),post)) :
    ∃ result : BitVec 64, value = .val (.word result) ∧ a.toNat ≤ result.toNat ∧ b.toNat ≤ result.toNat ∧
      result.toNat ≤ bound ∧ post = emptyLocalsHOLFinite state := by
  rw [evaluate_max_body state a b left right] at run
  have resultEq := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
  refine ⟨if b < a then a else b,resultEq.symm,?_,?_,?_,(Prod.mk.inj run).2.symm⟩
  all_goals split
  all_goals first
    | omega
    | (rename_i less; have natural : b.toNat < a.toNat := BitVec.lt_def.mp less; omega)
    | (rename_i less; have natural : ¬ b.toNat < a.toNat := fun h => less (BitVec.lt_def.mpr h); omega)

#print axioms max_body_returned_range
end InitECandidate.Runtime
