import InitECandidate.Runtime.AllocCostSSACallStage

/-!
# Source-only lexicographic induction harness for the executed-cost transfer

The counter recurses on `(s.termdep, s.clock, sizeOf p)` for the program it is
evaluating.  A source/target transfer cannot use a single program's measure,
because the callee body of a call is a code-table entry, not a subterm, and the
two sides evaluate different compiled programs.  The fix, as in the checked
`wordPathWork_permStack_variant`, is to induct **only on the source measure**
and to quantify every target program, state and relation *inside the motive*:
at a call the source `decClock`/`callEnv`/`pushEnv` step strictly drops the
source clock with the source termdep unchanged, so arbitrary callee syntax is
fine and the target measure never has to decrease.

This module provides the induction principle itself, so the per-constructor
transfer can be phrased as: "for all target programs and states, the motive
holds at the source state", proved by `lex3_induction` on the source triple.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-- The strict lexicographic order on triples of naturals, matching the
`termination_by (s.termdep, s.clock, sizeOf p)` measure of the counter. -/
def Lex3 (b1 b2 b3 a1 a2 a3 : Nat) : Prop :=
  b1 < a1 ∨ (b1 = a1 ∧ (b2 < a2 ∨ (b2 = a2 ∧ b3 < a3)))

/-- **Source-only lexicographic induction.**  Proving `P` for every triple from
a step that may use `P` at every strictly smaller triple (in `Lex3`).  Applied
with `P` quantifying the target program, target state and the relation between
the two runs, this is the source-measure induction used for the whole transfer:
no target measure occurs. -/
theorem lex3_induction (P : Nat × Nat × Nat → Prop)
    (h : ∀ a, (∀ b, Lex3 b.1 b.2.1 b.2.2 a.1 a.2.1 a.2.2 → P b) → P a) :
    ∀ a, P a := by
  rintro ⟨n1, n2, n3⟩
  revert n2 n3
  refine Nat.strongRecOn n1 ?_
  intro m1 ih1 n2 n3
  revert n3
  refine Nat.strongRecOn n2 ?_
  intro m2 ih2 n3
  refine Nat.strongRecOn n3 ?_
  intro m3 ih3
  refine h (m1, m2, m3) ?_
  rintro ⟨b1, b2, b3⟩ hb
  rcases hb with hlt | ⟨he1, hlt | ⟨he2, hlt3⟩⟩
  · exact ih1 b1 hlt b2 b3
  · subst he1
    exact ih2 b2 hlt b3
  · subst he1
    subst he2
    exact ih3 b3 hlt3

#print axioms lex3_induction

end InitECandidate.Runtime.FineCost
