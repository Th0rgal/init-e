import InitECandidate.Runtime.GuestCostCallRule
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

/-- A word-valued expression records exactly one copied word. -/
theorem resultWords_word (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (word : BitVec 64)
    (value : expressionValue s e = some (.val (.word word))) :
    resultWords s e = 1 := by
  unfold resultWords
  rw [value]
  simp [flattenHOL]

/-- A word-valued expression is recognised as a word. -/
theorem expressionIsWord_word (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    (word : BitVec 64) (value : expressionValue s e = some (.val (.word word))) :
    expressionIsWord s e = true := by
  unfold expressionIsWord
  rw [value]

/-- Constants cost one expression entry and one copied word. -/
theorem expressionCost_const (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (word : BitVec 64) :
    expressionCost coeff s (.const word) = coeff.expressions + coeff.movedWords := by
  unfold expressionCost
  rw [expressionEvents]
  rw [executionWork_score_cons, score_expression]
  simp [executionWork, WorkEvent.units, Work.score, Work.plus]

/-- Variable reads cost one entry and one copied word per copied value. -/
theorem expressionCost_var (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (kind : VarKind) (name : MlStringHOL) :
    expressionCost coeff s (.var kind name) =
      coeff.expressions + coeff.movedWords * resultWords s (.var kind name) +
        coeff.score (executionWork (globalEvents kind (resultWords s (.var kind name)))) := by
  unfold expressionCost
  rw [expressionEvents]
  rw [executionWork_score_cons, score_expression]
  cases kind <;> simp [globalEvents, executionWork, WorkEvent.units, Work.score, Work.plus] <;> omega

/-- Local reads retain their original expression/copy prices. -/
theorem expressionCost_local_var (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (name : MlStringHOL) :
    expressionCost coeff s (.var .local name) =
      coeff.expressions + coeff.movedWords * resultWords s (.var .local name) := by
  simpa [globalEvents, executionWork, Work.score] using expressionCost_var coeff s .local name

/-- Global reads additionally pay fixed setup and actual flattened words. -/
theorem expressionCost_global_var (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (name : MlStringHOL) :
    expressionCost coeff s (.var .global name) =
      coeff.expressions + coeff.movedWords * resultWords s (.var .global name) +
        coeff.globalAccesses + coeff.globalWords * resultWords s (.var .global name) := by
  have price := expressionCost_var coeff s .global name
  simp only [globalEvents, score_singleton, score_globalAccess] at price
  simpa only [Nat.add_assoc] using price

/-- The recorded events of a binary operator, as the score lemmas consume them. -/
theorem expressionEvents_op (s : PanSemStateFiniteExact 64 F) (op : BinOp)
    (left right : ExpHOL 64) :
    expressionEvents s (.op op [left, right]) =
      .expression :: (expressionEvents s left ++ (expressionEvents s right ++ [.scalar 2])) := by
  rw [expressionEvents]
  rw [expressionListEvents, expressionListEvents, expressionListEvents]
  simp

/-- A binary operator pays both operands plus one scalar operation per operand. -/
theorem expressionCost_op (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (op : BinOp) (left right : ExpHOL 64) :
    expressionCost coeff s (.op op [left, right]) =
      coeff.expressions + expressionCost coeff s left + expressionCost coeff s right +
        coeff.scalarOps * 2 := by
  unfold expressionCost
  rw [expressionEvents_op]
  rw [executionWork_score_cons, score_expression]
  rw [executionWork_score_append, executionWork_score_append]
  rw [score_singleton, score_scalar]
  omega

/-- A word comparison pays both operands plus one scalar operation. -/
theorem expressionCost_cmp (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (operator : Cmp) (left right : ExpHOL 64)
    (leftWord : expressionIsWord s left = true) (rightWord : expressionIsWord s right = true) :
    expressionCost coeff s (.cmp operator left right) =
      coeff.expressions + expressionCost coeff s left + expressionCost coeff s right +
        coeff.scalarOps := by
  unfold expressionCost
  rw [expressionEvents]
  simp only [leftWord, rightWord, Bool.and_self, ↓reduceIte]
  rw [executionWork_score_cons, score_expression]
  rw [executionWork_score_append, executionWork_score_append]
  rw [score_singleton, score_scalar]
  omega

#print axioms expressionCost_local_var
#print axioms expressionCost_global_var
#print axioms expressionCost_const
#print axioms expressionCost_var
#print axioms expressionCost_op
#print axioms expressionCost_cmp
end InitECandidate.Runtime.FineCost
