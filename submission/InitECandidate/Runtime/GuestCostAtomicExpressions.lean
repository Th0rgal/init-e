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

/-- A constant's executed price is its source price. -/
theorem expressionCost_const (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (word : BitVec 64) :
    expressionCost coeff s (.const word) = coeff.nativeCost * sourcePrice s (.const word) :=
  expressionCost_eq coeff s (.const word)

/-- A variable read's executed price is its source price. -/
theorem expressionCost_var (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (kind : VarKind) (name : MlStringHOL) :
    expressionCost coeff s (.var kind name) =
      coeff.nativeCost * sourcePrice s (.var kind name) :=
  expressionCost_eq coeff s (.var kind name)

/-- The recorded event list of a binary operator is its one source-price event. -/
theorem expressionEvents_op (s : PanSemStateFiniteExact 64 F) (op : BinOp)
    (left right : ExpHOL 64) :
    expressionEvents s (.op op [left, right]) =
      [.cost (sourcePrice s (.op op [left, right]))] := by
  rfl

/-- A binary operator's executed price is its source price. -/
theorem expressionCost_op (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (op : BinOp) (left right : ExpHOL 64) :
    expressionCost coeff s (.op op [left, right]) =
      coeff.nativeCost * sourcePrice s (.op op [left, right]) :=
  expressionCost_eq coeff s (.op op [left, right])

/-- A comparison's executed price is its source price. -/
theorem expressionCost_cmp (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (operator : Cmp) (left right : ExpHOL 64) :
    expressionCost coeff s (.cmp operator left right) =
      coeff.nativeCost * sourcePrice s (.cmp operator left right) :=
  expressionCost_eq coeff s (.cmp operator left right)

#print axioms expressionCost_const
#print axioms expressionCost_var
#print axioms expressionCost_op
#print axioms expressionCost_cmp
end InitECandidate.Runtime.FineCost
