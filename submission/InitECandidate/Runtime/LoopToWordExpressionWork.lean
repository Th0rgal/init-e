import InitECandidate.Runtime.LoopExpressionWork
import Flapjack.Pancake.Proofs.LoopToWord.CompExpPreservesEval
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopToWord

mutual
  def wordExpressionWork : WordLangExpHOL (BitVec 64) → Nat
    | .load address => 1 + wordExpressionWork address
    | .op _ args => 1 + wordExpressionsWork args
    | .shift _ left right => 1 + wordExpressionWork left + wordExpressionWork right
    | _ => 1
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  def wordExpressionsWork : List (WordLangExpHOL (BitVec 64)) → Nat
    | [] => 0
    | head :: tail => wordExpressionWork head + wordExpressionsWork tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Local charging makes this pass preserve expression work exactly. In
particular, topAddr pays five nodes locally rather than introducing a global
factor of five over every expression in the program. -/
theorem loop_to_word_expression_work (context : Spt Nat) :
    ∀ e : HolLoopExp 64, wordExpressionWork (compExpHOL context e) = loopValueWork e := by
  refine HolLoopExp.rec
    (motive_1 := fun e => wordExpressionWork (compExpHOL context e) = loopValueWork e)
    (motive_2 := fun es => wordExpressionsWork (es.map (compExpHOL context)) = loopValuesWork es)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value; simp [compExpHOL, wordExpressionWork, loopValueWork]
  · intro name; simp [compExpHOL, wordExpressionWork, loopValueWork]
  · intro store; simp [compExpHOL, wordExpressionWork, loopValueWork]
  · intro address ih; simp [compExpHOL, wordExpressionWork, loopValueWork, ih]
  · intro operator args ih; simp [compExpHOL, wordExpressionWork, loopValueWork, ih]
  · intro operator left right ihLeft ihRight
    simp [compExpHOL, wordExpressionWork, loopValueWork, ihLeft, ihRight]
  · simp [compExpHOL, wordExpressionWork, loopValueWork]
  · simp [compExpHOL, wordExpressionWork, wordExpressionsWork, loopValueWork]
  · simp [wordExpressionsWork, loopValuesWork]
  · intro head tail ihHead ihTail
    simp [wordExpressionsWork, loopValuesWork, ihHead, ihTail]

#print axioms loop_to_word_expression_work
end InitECandidate.Runtime.FineCost
