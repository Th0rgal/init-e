import InitECandidate.Runtime.GuestCostSequence
import InitECandidate.Runtime.GuestCostAtomicExpressions
import InitECandidate.Runtime.GasArithmetic
import InitECandidate.Runtime.ChargeGas
import InitECandidate.Runtime.GuestCostChargeFamily
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

/-- The saturating-add opcode helper: add the two words and return the maximum
word exactly when the addition carried. -/
noncomputable def addSatSumExpression : ExpHOL 64 :=
  .op BinOp.add [.var .local (ofString "a"), .var .local (ofString "b")]

noncomputable def addSatCarryExpression : ExpHOL 64 :=
  .cmp Cmp.lower (.var .local (ofString "s")) (.var .local (ofString "a"))

noncomputable def addSatMaximum : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 1)

/-- Value of the sum expression. -/
theorem eval_addSatSumExpression (s : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (hA : s.locals.lookup (ofString "a") = some (.val (.word a)))
    (hB : s.locals.lookup (ofString "b") = some (.val (.word b))) :
    expressionValue s addSatSumExpression = some (.val (.word (a + b))) := by
  classical
  unfold expressionValue addSatSumExpression
  simp [evalHOLExact, evalListHOLExact, toExact, hA, hB, wordOpHOL, wordOp, valueIsWord,
    valueWord]

/-- Value of the carry comparison, read from the declared sum. -/
theorem eval_addSatCarryExpression (s : PanSemStateFiniteExact 64 F) (sum a : BitVec 64)
    (hSum : s.locals.lookup (ofString "s") = some (.val (.word sum)))
    (hA : s.locals.lookup (ofString "a") = some (.val (.word a))) :
    expressionValue s addSatCarryExpression =
      some (.val (.word (if sum.toNat < a.toNat then 1 else 0))) := by
  classical
  unfold expressionValue addSatCarryExpression
  simp [evalHOLExact, toExact, hSum, hA,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]


/-- The compiled body of the saturating-add helper. -/
noncomputable def addSatTail : ProgHOL 64 :=
  .seq (.ite addSatCarryExpression (.return (.const addSatMaximum)) .skip)
    (.return (.var VarKind.local (ofString "s")))

/-- The declared body of the helper: the sum is bound under the name `s`. -/
noncomputable def addSatDeclaredBody : ProgHOL 64 :=
  .dec (ofString "s") .one addSatSumExpression addSatTail

/-- Post state of a helper run that returned a word: locals dropped and the
previous `s` restored. -/
noncomputable def addSatReturnedPost (s : PanSemStateFiniteExact 64 F) (sum : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  let post := emptyLocalsHOLFinite (setVarHOLFinite (ofString "s") (.val (.word sum)) s)
  { post with locals := (HolFiniteMapExact.resVarEq post.locals
      (ofString "s", s.locals.lookup (ofString "s"))) }

/-- Recorded work of the carry path of the helper. -/
noncomputable def addSatCarryEvents (s : PanSemStateFiniteExact 64 F) (sum : BitVec 64) :
    List WorkEvent :=
  let entry := setVarHOLFinite (ofString "s") (.val (.word sum)) s
  let guardEvents := expressionEvents entry addSatCarryExpression
  let retEvents := .statement :: (expressionEvents entry (.const addSatMaximum) ++
    [.copy (flattenHOL (.val (.word addSatMaximum))).length])
  let tailEvents := .statement :: (.statement :: (guardEvents ++ retEvents))
  .statement :: (expressionEvents s addSatSumExpression ++
    [.copy (flattenHOL (.val (.word sum))).length, .frame 1] ++ tailEvents ++
    [.copy (((s.locals.lookup (ofString "s")).map
      (fun previous => (flattenHOL previous).length)).getD 0)])

/-- Recorded work of the no-carry path of the helper. -/
noncomputable def addSatNoCarryEvents (s : PanSemStateFiniteExact 64 F) (sum : BitVec 64) :
    List WorkEvent :=
  let entry := setVarHOLFinite (ofString "s") (.val (.word sum)) s
  let guardEvents := .statement :: (expressionEvents entry addSatCarryExpression ++ [.statement])
  let retEvents := .statement :: (expressionEvents entry (.var VarKind.local (ofString "s")) ++
    [.copy (flattenHOL (.val (.word sum))).length])
  let tailEvents := .statement :: (guardEvents ++ retEvents)
  .statement :: (expressionEvents s addSatSumExpression ++
    [.copy (flattenHOL (.val (.word sum))).length, .frame 1] ++ tailEvents ++
    [.copy (((s.locals.lookup (ofString "s")).map
      (fun previous => (flattenHOL previous).length)).getD 0)])

/-- The carry path: the sum overflowed, so the helper returns the maximum word. -/
theorem addSat_carry_run (s : PanSemStateFiniteExact 64 F) (a b sum : BitVec 64)
    (hA : s.locals.lookup (ofString "a") = some (.val (.word a)))
    (hB : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (hSum : sum = a + b)
    (carry : sum.toNat < a.toNat) :
    StatementRun s addSatDeclaredBody (some (.returned (.val (.word addSatMaximum))))
      (addSatReturnedPost s sum) (addSatCarryEvents s sum) := by
  classical
  let entry := setVarHOLFinite (ofString "s") (.val (.word sum)) s
  have names : ofString "a" ≠ ofString "s" := by decide_cbv
  have entryA : entry.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entry, setVarHOLFinite, FUPDATE, names, Ne.symm names] using hA
  have entryS : entry.locals.lookup (ofString "s") = some (.val (.word sum)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have initValue : expressionValue s addSatSumExpression = some (.val (.word sum)) := by
    rw [hSum]
    exact eval_addSatSumExpression s a b hA hB
  have init : CostedExpressionRun s addSatSumExpression (some (.val (.word sum)))
      (expressionEvents s addSatSumExpression) :=
    costedExpression_events s _ _ initValue
  have guardValue : expressionValue entry addSatCarryExpression = some (.val (.word 1)) := by
    have := eval_addSatCarryExpression entry sum a (by simpa [entry] using entryS) entryA
    rw [this]
    simp [carry]
  have guard : CostedExpressionRun entry addSatCarryExpression (some (.val (.word 1)))
      (expressionEvents entry addSatCarryExpression) :=
    costedExpression_events entry addSatCarryExpression _ guardValue
  have payload : CostedExpressionRun entry (.const addSatMaximum)
      (some (.val (.word addSatMaximum))) (expressionEvents entry (.const addSatMaximum)) :=
    costedExpression_events entry _ _ (by simp [expressionValue, evalHOLExact])
  have bodyRun : StatementRun entry (.return (.const addSatMaximum))
      (some (.returned (.val (.word addSatMaximum)))) (emptyLocalsHOLFinite entry)
      (.statement :: (expressionEvents entry (.const addSatMaximum) ++
        [.copy (flattenHOL (.val (.word addSatMaximum))).length])) :=
    StatementRun.returnValue (expression := .const addSatMaximum) payload
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have tailRun : StatementRun entry addSatTail
      (some (.returned (.val (.word addSatMaximum)))) (emptyLocalsHOLFinite entry)
      (.statement :: (.statement :: (expressionEvents entry addSatCarryExpression ++
        (.statement :: (expressionEvents entry (.const addSatMaximum) ++
          [.copy (flattenHOL (.val (.word addSatMaximum))).length]))))) := by
    unfold addSatTail
    exact StatementRun.seqStop (by simp)
      (StatementRun.iteYes (post := emptyLocalsHOLFinite entry)
        (yes := .return (.const addSatMaximum)) (no := .skip) guard (by decide) bodyRun)
  have shapeMatch : shapeEqHOL .one (shapeOfHOLExact (.val (.word sum))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  refine StatementRun.declareValue (name := ofString "s") (shape := .one)
    (initializer := addSatSumExpression) (body := addSatTail) init shapeMatch ?_
  simpa [addSatCarryEvents, addSatDeclaredBody, entry] using tailRun

/-- The no-carry path: the helper returns the wrapped sum it declared. -/
theorem addSat_noCarry_run (s : PanSemStateFiniteExact 64 F) (a b sum : BitVec 64)
    (hA : s.locals.lookup (ofString "a") = some (.val (.word a)))
    (hB : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (hSum : sum = a + b)
    (noCarry : ¬ sum.toNat < a.toNat) :
    StatementRun s addSatDeclaredBody (some (.returned (.val (.word sum))))
      (addSatReturnedPost s sum) (addSatNoCarryEvents s sum) := by
  classical
  let entry := setVarHOLFinite (ofString "s") (.val (.word sum)) s
  have names : ofString "a" ≠ ofString "s" := by decide_cbv
  have entryA : entry.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entry, setVarHOLFinite, FUPDATE, names, Ne.symm names] using hA
  have entryS : entry.locals.lookup (ofString "s") = some (.val (.word sum)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have initValue : expressionValue s addSatSumExpression = some (.val (.word sum)) := by
    rw [hSum]
    exact eval_addSatSumExpression s a b hA hB
  have init : CostedExpressionRun s addSatSumExpression (some (.val (.word sum)))
      (expressionEvents s addSatSumExpression) :=
    costedExpression_events s _ _ initValue
  have guardValue : expressionValue entry addSatCarryExpression = some (.val (.word 0)) := by
    have := eval_addSatCarryExpression entry sum a (by simpa [entry] using entryS) entryA
    rw [this]
    simp [noCarry]
  have guard : CostedExpressionRun entry addSatCarryExpression (some (.val (.word 0)))
      (expressionEvents entry addSatCarryExpression) :=
    costedExpression_events entry addSatCarryExpression _ guardValue
  have retValue : expressionValue entry (.var VarKind.local (ofString "s")) =
      some (.val (.word sum)) := by
    simp [expressionValue, evalHOLExact, entry, setVarHOLFinite, FUPDATE]
  have ret : CostedExpressionRun entry (.var VarKind.local (ofString "s"))
      (some (.val (.word sum)))
      (expressionEvents entry (.var VarKind.local (ofString "s"))) :=
    costedExpression_events entry _ _ retValue
  have bodyRun : StatementRun entry (.return (.var VarKind.local (ofString "s")))
      (some (.returned (.val (.word sum)))) (emptyLocalsHOLFinite entry)
      (.statement :: (expressionEvents entry (.var VarKind.local (ofString "s")) ++
        [.copy (flattenHOL (.val (.word sum))).length])) :=
    StatementRun.returnValue (expression := .var VarKind.local (ofString "s")) ret
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have tailRun : StatementRun entry addSatTail
      (some (.returned (.val (.word sum)))) (emptyLocalsHOLFinite entry)
      (.statement :: ((.statement :: (expressionEvents entry addSatCarryExpression ++
        [.statement])) ++
        (.statement :: (expressionEvents entry (.var VarKind.local (ofString "s")) ++
          [.copy (flattenHOL (.val (.word sum))).length])))) := by
    unfold addSatTail
    exact StatementRun.seqNext
      (StatementRun.iteNo (condition := addSatCarryExpression)
        (yes := .return (.const addSatMaximum)) (no := .skip) guard
        (StatementRun.skip (s := entry))) bodyRun
  have shapeMatch : shapeEqHOL .one (shapeOfHOLExact (.val (.word sum))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  refine StatementRun.declareValue (name := ofString "s") (shape := .one)
    (initializer := addSatSumExpression) (body := addSatTail) init shapeMatch ?_
  simpa [addSatNoCarryEvents, addSatDeclaredBody, entry] using tailRun


/-- Explicit price of the carry path of the saturating-add helper. -/
theorem addSatCarryEvents_score (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (sum : BitVec 64) :
    coeff.score (executionWork (addSatCarryEvents s sum)) ≤
      let entry := setVarHOLFinite (ofString "s") (.val (.word sum)) s
      16 * coeff.statements +
        expressionCost coeff s addSatSumExpression +
        coeff.movedWords * (flattenHOL (.val (.word sum))).length + coeff.frameSlots +
        expressionCost coeff entry addSatCarryExpression +
        expressionCost coeff entry (.const addSatMaximum) +
        coeff.movedWords * (flattenHOL (.val (.word addSatMaximum))).length +
        coeff.movedWords * (((s.locals.lookup (ofString "s")).map
          (fun previous => (flattenHOL previous).length)).getD 0) := by
  unfold addSatCarryEvents expressionCost
  simp only [executionWork_score_cons, executionWork_score_append, score_statement,
    score_copy, score_frame, score_memory, score_singleton, score_expression,
    executionWork_nil_score, List.append_nil]
  omega

/-- Explicit price of the no-carry path of the saturating-add helper. -/
theorem addSatNoCarryEvents_score (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (sum : BitVec 64) :
    coeff.score (executionWork (addSatNoCarryEvents s sum)) ≤
      let entry := setVarHOLFinite (ofString "s") (.val (.word sum)) s
      16 * coeff.statements +
        expressionCost coeff s addSatSumExpression +
        coeff.movedWords * (flattenHOL (.val (.word sum))).length + coeff.frameSlots +
        expressionCost coeff entry addSatCarryExpression +
        expressionCost coeff entry (.var VarKind.local (ofString "s")) +
        coeff.movedWords * (flattenHOL (.val (.word sum))).length +
        coeff.movedWords * (((s.locals.lookup (ofString "s")).map
          (fun previous => (flattenHOL previous).length)).getD 0) := by
  unfold addSatNoCarryEvents expressionCost
  simp only [executionWork_score_cons, executionWork_score_append, score_statement,
    score_copy, score_frame, score_memory, score_singleton, score_expression,
    executionWork_nil_score, List.append_nil]
  omega

#print axioms addSatCarryEvents_score
#print axioms addSatNoCarryEvents_score

#print axioms addSat_carry_run
#print axioms addSat_noCarry_run
