import InitECandidate.Runtime.AllocCostOptimizer
import Flapjack.Compiler.Backend.WordCse.Transform
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.WordToStack

/-!
# Common-subexpression elimination on the straight-line fragment

`wordCse` can replace one instruction or `Get` by a single rematerialization
move.  Every such replacement adds at most one local node; `cseSites` counts
exactly the sites where that can happen.  No whole-program knowledge table or
fact set is charged.
-/

/-- Instructions, `Get`s and heap reads, the only CSE replacement sites. -/
def cseSites : WordLangProgHOL (BitVec 64) → Nat
  | .inst _ => 1
  | .get _ _ => 1
  | .opCurrHeap _ _ _ => 1
  | .seq first second => cseSites first + cseSites second
  | _ => 0
termination_by p => sizeOf p

theorem addToDataAux_nodeCost (data : Knowledge) (destination : Nat) (key : List Nat)
    (original : WordLangProgHOL (BitVec 64)) (small : wordNodeCost original ≤ 1) :
    wordNodeCost (addToDataAux data destination key original).2 ≤ 2 := by
  simp only [addToDataAux]
  repeat' (first | split | simp [wordNodeCost])
  all_goals omega

theorem wordCseInst_nodeCost (data : Knowledge) (instruction : HolInst 64) :
    wordNodeCost (wordCseInst data instruction).2 ≤ 2 := by
  cases instruction with
  | skip => simp [wordCseInst, wordNodeCost]
  | const destination value =>
    simp only [wordCseInst]
    repeat' (first | split | simp [addToDataConst, wordNodeCost])
    all_goals omega
  | arith operation =>
    cases operation <;> simp only [wordCseInst]
    all_goals
      repeat' (first | split | simp [addToData, addToDataAux, wordNodeCost])
      all_goals omega
  | mem operation destination address =>
    cases operation <;> simp only [wordCseInst]
    all_goals
      repeat' (first | split | simp [addToDataAux, addToLoadAux, wordNodeCost])
      all_goals omega

theorem getClause_nodeCost (data : Knowledge) (destination : Nat) (store : WordStoreHOL) :
    wordNodeCost (getClause data destination store).2 ≤ 2 := by
  simp only [getClause]
  repeat' (first | split | simp [wordNodeCost])
  all_goals omega

theorem wordCse_straight_nodeCost (data : Knowledge) (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) :
    wordNodeCost (wordCse data p).2 ≤ wordNodeCost p + cseSites p := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp [wordCse, wordNodeCost, cseSites]
  case move priority moves => simp [wordCse, wordNodeCost, cseSites]
  case inst instruction =>
    have bound := wordCseInst_nodeCost data (HolInst.ofWordLangInst instruction)
    simp only [wordCse, wordNodeCost, cseSites]
    omega
  case get destination store =>
    have bound := getClause_nodeCost data destination store
    simp only [wordCse, wordNodeCost, cseSites]
    omega
  case opCurrHeap operator destination source =>
    simp only [wordCse]
    split
    · simp [wordNodeCost, cseSites]
    · have bound := addToDataAux_nodeCost
        (registerRead (invalidateData data destination)
          (canonicalRegs' destination (invalidateData data destination) source))
        destination
        (opCurrHeapToNumList operator
          (canonicalRegs' destination (invalidateData data destination) source))
        (.opCurrHeap operator destination source) (by simp [wordNodeCost])
      simp only [wordNodeCost, cseSites]
      omega
  case seq first second =>
    rcases firstRun : wordCse data first with ⟨data', first'⟩
    have firstBound := wordCse_straight_nodeCost data first supported.1
    rw [firstRun] at firstBound
    dsimp only at firstBound
    have secondBound := wordCse_straight_nodeCost data' second supported.2
    rw [wordCse, firstRun]
    simp only [wordNodeCost, cseSites]
    omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

theorem wordCommonSubexpElim_straight_nodeCost (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) :
    wordNodeCost (wordCommonSubexpElim p) ≤ wordNodeCost p + cseSites p :=
  wordCse_straight_nodeCost emptyData p supported

#print axioms wordCommonSubexpElim_straight_nodeCost
#print axioms wordCse_straight_nodeCost
end InitECandidate.Runtime.FineCost
