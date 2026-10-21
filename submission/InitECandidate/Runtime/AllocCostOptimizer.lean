import InitECandidate.Runtime.AllocCostExecuted
import Flapjack.Compiler.Backend.WordRemove
import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Compiler.Backend.WordCopy
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc Flapjack.Compiler.Backend.WordRemove
open Flapjack.Compiler.Backend.WordCopy Flapjack.Compiler.Backend.WordInst
open InitECandidate.Runtime.WordToStack

/-!
# Deleting Word optimizers do not amplify the local envelope

`removeMustTerminate`, dead-code removal and copy propagation can only drop
instructions, shorten parallel moves or replace a `Get` by one singleton move.
They are therefore bounded by `wordNodeCost` plus one local unit per `Get`
which copy propagation may materialize as a move.  These lemmas cover the
straight-line fragment grammar used by the SSA/three-to-two composition.
-/

/-- `remove_must_terminate` only deletes the `MustTerminate` wrapper. -/
theorem removeMustTerminate_nodeCost (p : WordLangProgHOL (BitVec 64)) :
    wordNodeCost (removeMustTerminate p) ≤ wordNodeCost p := by
  cases p
  case seq first second =>
    have firstBound := removeMustTerminate_nodeCost first
    have secondBound := removeMustTerminate_nodeCost second
    simp [removeMustTerminate, wordNodeCost]; omega
  case ite operator condition right thenBranch elseBranch =>
    have thenBound := removeMustTerminate_nodeCost thenBranch
    have elseBound := removeMustTerminate_nodeCost elseBranch
    simp [removeMustTerminate, wordNodeCost]; omega
  case mustTerminate body =>
    have bound := removeMustTerminate_nodeCost body
    simp [removeMustTerminate, wordNodeCost]; omega
  case call returns target arguments handler =>
    cases returns with
    | none =>
      cases handler with
      | none => simp [removeMustTerminate, wordNodeCost]
      | some handlerData =>
        rcases handlerData with ⟨reg, code, l1, l2⟩
        have bound := removeMustTerminate_nodeCost code
        simp [removeMustTerminate, wordNodeCost]; omega
    | some returnData =>
      rcases returnData with ⟨values, cutsets, returnCode, l1, l2⟩
      cases handler with
      | none =>
        have bound := removeMustTerminate_nodeCost returnCode
        simp [removeMustTerminate, wordNodeCost]; omega
      | some handlerData =>
        rcases handlerData with ⟨reg, code, l1', l2'⟩
        have returnBound := removeMustTerminate_nodeCost returnCode
        have handlerBound := removeMustTerminate_nodeCost code
        simp [removeMustTerminate, wordNodeCost]; omega
  case loop liveIn body liveOut =>
    have bound := removeMustTerminate_nodeCost body
    simp [removeMustTerminate, wordNodeCost]; omega
  all_goals simp [removeMustTerminate, wordNodeCost]
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- Dead-code removal on the straight-line grammar only drops work. -/
theorem removeDead_straight_nodeCost (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) (live : NumSet) (nlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet)) :
    wordNodeCost (removeDead p live nlive lt).1 ≤ wordNodeCost p := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp [removeDead, wordNodeCost]
  case move priority moves =>
    simp only [removeDead]
    split
    · simp [wordNodeCost]
    · simp only [wordNodeCost]
      have := List.length_filter_le (fun p => decide (sptLookup p.1 live = some ())) moves
      omega
  case inst instruction =>
    simp only [removeDead]
    split <;> simp [wordNodeCost]
  case get destination store =>
    simp only [removeDead]
    split <;> simp [wordNodeCost]
  case opCurrHeap operator destination source =>
    simp only [removeDead]
    split <;> simp [wordNodeCost]
  case seq first second =>
    rcases secondRun : removeDead second live nlive lt with ⟨second', secondLive, secondNlive⟩
    have secondBound := removeDead_straight_nodeCost second supported.2 live nlive lt
    rw [secondRun] at secondBound
    dsimp only at secondBound
    rcases firstRun : removeDead first secondLive secondNlive lt with ⟨first', firstLive, firstNlive⟩
    have firstBound := removeDead_straight_nodeCost first supported.1 secondLive secondNlive lt
    rw [firstRun] at firstBound
    dsimp only at firstBound
    simp only [removeDead, secondRun, firstRun]
    by_cases hfirst : first' = WordLangProgHOL.skip
    · subst first'
      simp only [wordNodeCost]; omega
    · by_cases hsecond : second' = WordLangProgHOL.skip
      · subst second'
        simp only [wordNodeCost]; omega
      · simp [hfirst, hsecond, wordNodeCost]
        omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

theorem copyPropMove_length (moves : List (Nat × Nat)) (cs : CopyState) :
    (copyPropMove moves cs).1.length = moves.length := by
  induction moves with
  | nil => simp [copyPropMove]
  | cons head tail ih =>
    rcases head with ⟨source, target⟩
    simp [copyPropMove, ih]

theorem copyPropInst_nodeCost (instruction : WordLangInst (BitVec 64)) (cs : CopyState) :
    wordNodeCost (copyPropInst instruction cs).1 ≤ 1 := by
  cases instruction with
  | skip => simp [copyPropInst, wordNodeCost]
  | const reg value => simp [copyPropInst, wordNodeCost]
  | arith operation => cases operation <;> simp [copyPropInst, wordNodeCost]
  | mem operation destination address =>
    cases operation <;> simp [copyPropInst, wordNodeCost]

/-- `Get` nodes, the only copy-propagation site that can become a move. -/
def copyPropSites : WordLangProgHOL (BitVec 64) → Nat
  | .get _ _ => 1
  | .seq first second => copyPropSites first + copyPropSites second
  | _ => 0
termination_by p => sizeOf p

theorem copyPropProg_straight_nodeCost (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) (cs : CopyState) :
    wordNodeCost (copyPropProg p cs).1 ≤ wordNodeCost p + copyPropSites p := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp [copyPropProg, wordNodeCost, copyPropSites]
  case move priority moves =>
    simp only [copyPropProg]
    split
    · simp only [wordNodeCost, copyPropSites]
      rw [copyPropMove_length]; omega
    · simp only [wordNodeCost, copyPropSites]; omega
  case inst instruction =>
    simp only [copyPropProg]
    have bound := copyPropInst_nodeCost instruction cs
    simp only [wordNodeCost, copyPropSites]
    omega
  case get destination store =>
    simp only [copyPropProg]
    split
    · simp only [wordNodeCost, copyPropSites]; omega
    · split
      · simp only [wordNodeCost, copyPropSites]
        rw [copyPropMove_length]
        simp
      · simp only [wordNodeCost, copyPropSites]; omega
  case opCurrHeap operator destination source =>
    simp [copyPropProg, wordNodeCost, copyPropSites]
  case seq first second =>
    rcases firstRun : copyPropProg first cs with ⟨first', cs'⟩
    have firstBound := copyPropProg_straight_nodeCost first supported.1 cs
    rw [firstRun] at firstBound
    dsimp only at firstBound
    have secondBound := copyPropProg_straight_nodeCost second supported.2 cs'
    rw [copyPropProg, firstRun]
    simp only [wordNodeCost, copyPropSites]
    omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

theorem copyProp_straight_nodeCost (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) :
    wordNodeCost (copyProp p) ≤ wordNodeCost p + copyPropSites p :=
  copyPropProg_straight_nodeCost p supported emptyEq

#print axioms copyProp_straight_nodeCost
#print axioms removeDead_straight_nodeCost
#print axioms removeMustTerminate_nodeCost
end InitECandidate.Runtime.FineCost
