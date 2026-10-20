import InitECandidate.Runtime.AllocCostCse
import Flapjack.Compiler.Backend.WordUnreach
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordUnreach
open InitECandidate.Runtime.WordToStack

/-!
# Unreachable-code cleanup on the straight-line fragment

`removeUnreach` right-associates sequences and merges adjacent moves.  On the
straight-line fragment it only deletes the trailing `Skip`, shortens merged
moves and reassociates `Seq`; the generalized statement below charges one
local node for the reassociation wrapper, so the whole pass costs at most a
constant two nodes over the original envelope.
-/

theorem anub_length_le {α β : Type} [DecidableEq α] (entries : List (α × β))
    (seen : List α) : (anub entries seen).length ≤ entries.length := by
  induction entries generalizing seen with
  | nil => simp [anub]
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    simp only [anub]
    split
    · exact Nat.le_trans (ih seen) (Nat.le_succ _)
    · have tailBound := ih (key :: seen)
      simp only [List.length_cons]
      omega

theorem mergeMoves_length_le (first second : List (Nat × Nat)) :
    (mergeMoves first second).length ≤ first.length + second.length := by
  let mapped := second.map (fun x =>
    match sptAListLookup x.snd first with
    | none => (x.fst, x.snd)
    | some v => (x.fst, v))
  have step : (mergeMoves first second).length = (anub (mapped ++ first) []).length := rfl
  rw [step]
  calc
    (anub (mapped ++ first) []).length ≤ (mapped ++ first).length :=
      anub_length_le _ _
    _ = second.length + first.length := by simp [mapped]
    _ = first.length + second.length := by omega

theorem simpSeq_straight_nodeCost (first second : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment first = true) :
    wordNodeCost (simpSeq first second) ≤
      wordNodeCost first + wordNodeCost second + 1 := by
  cases first <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip =>
    by_cases hskip : second = WordLangProgHOL.skip <;>
      simp [simpSeq, hskip, wordNodeCost] <;> omega
  case inst instruction =>
    by_cases hskip : second = WordLangProgHOL.skip
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
  case get destination store =>
    by_cases hskip : second = WordLangProgHOL.skip
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
  case opCurrHeap operator destination source =>
    by_cases hskip : second = WordLangProgHOL.skip
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
  case seq left right =>
    by_cases hskip : second = WordLangProgHOL.skip
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
  case move priority moves =>
    by_cases hskip : second = WordLangProgHOL.skip
    · simp [simpSeq, hskip, wordNodeCost] <;> omega
    · cases second with
      | move otherPriority otherMoves =>
        have mergedBound := mergeMoves_length_le moves otherMoves
        simp [simpSeq, hskip, destSeqMove, wordNodeCost] <;> omega
      | seq first rest =>
        cases first with
        | move otherPriority otherMoves =>
          have mergedBound := mergeMoves_length_le moves otherMoves
          simp [simpSeq, hskip, destSeqMove, wordNodeCost]
          by_cases hrest : rest = WordLangProgHOL.skip <;>
            simp [hrest, wordNodeCost] <;> omega
        | _ =>
          simp [simpSeq, hskip, destSeqMove, wordNodeCost] <;> omega
      | _ =>
        simp [simpSeq, hskip, destSeqMove, wordNodeCost] <;> omega

theorem seqAssocRight_straight_nodeCost (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) (acc : WordLangProgHOL (BitVec 64)) :
    wordNodeCost (seqAssocRight p acc) ≤ wordNodeCost p + wordNodeCost acc + 1 := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip =>
    simp [seqAssocRight]
    omega
  case inst instruction =>
    exact simpSeq_straight_nodeCost (.inst instruction) acc (by simp [wordStraightFragment])
  case get destination store =>
    exact simpSeq_straight_nodeCost (.get destination store) acc (by simp [wordStraightFragment])
  case opCurrHeap operator destination source =>
    exact simpSeq_straight_nodeCost (.opCurrHeap operator destination source) acc (by simp [wordStraightFragment])
  case move priority moves =>
    exact simpSeq_straight_nodeCost (.move priority moves) acc (by simp [wordStraightFragment])
  case seq first second =>
    have secondBound := seqAssocRight_straight_nodeCost second supported.2 acc
    have firstBound := seqAssocRight_straight_nodeCost first supported.1
      (seqAssocRight second acc)
    simp only [seqAssocRight, wordNodeCost]
    omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

theorem removeUnreach_straight_nodeCost (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) :
    wordNodeCost (removeUnreach p) ≤ wordNodeCost p + 2 := by
  have bound := seqAssocRight_straight_nodeCost p supported .skip
  simpa [removeUnreach, wordNodeCost] using bound

#print axioms removeUnreach_straight_nodeCost
#print axioms simpSeq_straight_nodeCost
end InitECandidate.Runtime.FineCost
