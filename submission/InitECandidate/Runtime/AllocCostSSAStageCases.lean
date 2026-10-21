import InitECandidate.Runtime.AllocCostSSASourceLex

/-!
# Constructor cases of the executed-cost stage producer

The producer quantifies the target program, target state and the allocator
relation inside the motive and inducts on the source measure with
`lex3_induction`.  These are the base cases: constructors whose clause charges
only the node price (`| _ => price p s` in the counter), so the case reduces to
the local node-price comparison, as the first checked constructor case.

Everything is price-parametric and relation-parametric; the relation only has to
supply the stack agreement used by the call and handler legs.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-- `skip` charges only its node price. -/
theorem wec_skip {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost price .skip s = price .skip s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction)

/-- Base case of the stage producer at `skip`: once both sides are known to be
`skip`, the transfer is exactly the local node-price comparison. -/
theorem wec_stage_skip_case {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (budget : WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) → Nat)
    (q : WordLangProgHOL (BitVec 64)) (s t : WordSemStateFiniteExact 64 C F)
    (hq : q = .skip)
    (hb : price q t ≤ price .skip s + budget .skip q) :
    wordExecutionCost price q t ≤ wordExecutionCost price .skip s + budget .skip q := by
  subst hq
  rw [wec_skip price t, wec_skip price s]
  exact hb

#print axioms wec_skip
#print axioms wec_stage_skip_case

end InitECandidate.Runtime.FineCost
