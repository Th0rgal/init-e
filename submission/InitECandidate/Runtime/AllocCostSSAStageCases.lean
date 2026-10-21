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

/-- `inst` charges only its node price (`WordLangInst` is indexed by the word
type, `WordLangInst (BitVec 64)` for this counter). -/
theorem wec_inst {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (i : WordLangInst (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost price (.inst i) s = price (.inst i) s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction)

/-- `move` charges only its node price; its parallel-move size is priced inside
`price`, not by an extra recursive term. -/
theorem wec_move {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost price (.move pri moves) s = price (.move pri moves) s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction)

/-- Stage base case at `inst`. -/
theorem wec_stage_inst_case {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (budget : WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) → Nat)
    (i j : WordLangInst (BitVec 64)) (s t : WordSemStateFiniteExact 64 C F)
    (hb : price (.inst j) t ≤ price (.inst i) s + budget (.inst i) (.inst j)) :
    wordExecutionCost price (.inst j) t ≤
      wordExecutionCost price (.inst i) s + budget (.inst i) (.inst j) := by
  rw [wec_inst price j t, wec_inst price i s]
  exact hb

/-- Stage base case at `move`. -/
theorem wec_stage_move_case {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (budget : WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) → Nat)
    (pri pri' : Nat) (moves moves' : List (Nat × Nat))
    (s t : WordSemStateFiniteExact 64 C F)
    (hb : price (.move pri' moves') t ≤
      price (.move pri moves) s + budget (.move pri moves) (.move pri' moves')) :
    wordExecutionCost price (.move pri' moves') t ≤
      wordExecutionCost price (.move pri moves) s +
        budget (.move pri moves) (.move pri' moves') := by
  rw [wec_move price pri' moves' t, wec_move price pri moves s]
  exact hb

#print axioms wec_inst
#print axioms wec_move
#print axioms wec_stage_inst_case
#print axioms wec_stage_move_case
#print axioms wec_skip
#print axioms wec_stage_skip_case

end InitECandidate.Runtime.FineCost
