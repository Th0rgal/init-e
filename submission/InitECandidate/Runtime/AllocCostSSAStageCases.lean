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

/-- **`seq` stage case, both halves falling through.**  Both first halves
return `none`, so each second half runs on its own reached middle state; the
recursive costs are the two induction hypotheses at those states, and only the
node price is extra. -/
theorem wec_seq_stage_none {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (first second firstT secondT : WordLangProgHOL (BitVec 64))
    (s t midS midT : WordSemStateFiniteExact 64 C F)
    (nodeBudget b1 b2 : Nat)
    (hs : fixClock s (evaluate first s) = (none, midS))
    (ht : fixClock t (evaluate firstT t) = (none, midT))
    (hnode : price (.seq firstT secondT) t ≤ price (.seq first second) s + nodeBudget)
    (hfirst : wordExecutionCost price firstT t ≤ wordExecutionCost price first s + b1)
    (hsecond : wordExecutionCost price secondT midT ≤
      wordExecutionCost price second midS + b2) :
    wordExecutionCost price (.seq firstT secondT) t ≤
      wordExecutionCost price (.seq first second) s + (nodeBudget + (b1 + b2)) := by
  rw [wordExecutionCost]
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  rw [ht]
  try dsimp only
  rw [hs]
  try dsimp only
  omega

/-- **`loop` case of the stage producer.**  The whole-loop transfer consumes
the one-step premise (whose body clause is the induction hypothesis at the
source cut state) and charges the recursive per-iteration extra at the source
clock; the loop node's own price is discharged exactly by the native instance. -/
theorem wec_stage_loop_case {C F : Type}
    (names targetNames exits targetExits : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64))
    (bodyBudget backBudget : Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (step : WecLoopStep nativeWordPrice names targetNames body targetBody R bodyBudget)
    (s t : WordSemStateFiniteExact 64 C F) (rel : R s t) :
    wordExecutionCost nativeWordPrice (.loop targetNames targetBody targetExits) t ≤
      wordExecutionCost nativeWordPrice (.loop names body exits) s +
        wecLoopExtra nativeWordPrice body names bodyBudget backBudget s :=
  wecLoop_executed_transfer_native names targetNames exits targetExits body targetBody
    bodyBudget backBudget R step s t rel

/-- **`call` case (returning, result branch) of the stage producer.**  The
allocated call costs no more than the source call once its three components
compare; the callee is the same syntax tree on both sides by `stage_findCode`,
so the body component is the induction hypothesis at the reached entry state and
the continuation component at the reached popped state. -/
theorem wec_stage_call_case {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t)
    (nodeT nodeS bodyT bodyS contT contS : Nat)
    (hcallT : wordExecutionCost nativeWordPrice
      (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
        nodeT + bodyT + contT)
    (hcallS : wordExecutionCost nativeWordPrice
      (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
        nodeS + bodyS + contS)
    (hnode : nodeT ≤ nodeS) (hbody : bodyT ≤ bodyS) (hcont : contT ≤ contS) :
    wordExecutionCost nativeWordPrice
        (.call (some (values, names, retCode, l1, l2)) dest args handler) t ≤
      wordExecutionCost nativeWordPrice
        (.call (some (values, names, retCode, l1, l2)) dest args handler) s :=
  ssaCall_returning_cost_stage ssa next values names retCode l1 l2 dest args handler
    s t rel nodeT nodeS bodyT bodyS contT contS hcallT hcallS hnode hbody hcont

#print axioms wec_stage_loop_case
#print axioms wec_stage_call_case
#print axioms wec_seq_stage_none
#print axioms wec_inst
#print axioms wec_move
#print axioms wec_stage_inst_case
#print axioms wec_stage_move_case
#print axioms wec_skip
#print axioms wec_stage_skip_case

end InitECandidate.Runtime.FineCost
