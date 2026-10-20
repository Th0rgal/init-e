import InitECandidate.Runtime.PanExpressionWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Size-aware statement traces. Recursive control rules expose every guard
expression and only the statements on the executed branch. -/
inductive StatementRun {F : Type} : PanSemStateFiniteExact 64 F → ProgHOL 64 →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List WorkEvent → Prop where
  | skip (s) : StatementRun s .skip none s [.statement]
  | seqNext {s first middle second r post left right}
      (one : StatementRun s first none middle left)
      (two : StatementRun middle second r post right) :
      StatementRun s (.seq first second) r post (.statement :: (left ++ right))
  | seqStop {s first second r post left} (terminal : r ≠ none)
      (one : StatementRun s first r post left) :
      StatementRun s (.seq first second) r post (.statement :: left)
  | iteYes {s condition yes no value guardEvents r post bodyEvents}
      (guard : ExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0)
      (body : StatementRun s yes r post bodyEvents) :
      StatementRun s (.ite condition yes no) r post
        (.statement :: (guardEvents ++ bodyEvents))
  | iteNo {s condition yes no guardEvents r post bodyEvents}
      (guard : ExpressionRun s condition (some (.val (.word 0))) guardEvents)
      (body : StatementRun s no r post bodyEvents) :
      StatementRun s (.ite condition yes no) r post
        (.statement :: (guardEvents ++ bodyEvents))

  | breakStmt (s) : StatementRun s .break (some .break) s [.statement]
  | continueStmt (s) : StatementRun s .continue (some .continue) s [.statement]
  | whileFalse {s condition body guardEvents}
      (guard : ExpressionRun s condition (some (.val (.word 0))) guardEvents) :
      StatementRun s (.while condition body) none s (.statement :: guardEvents)
  | whileNext {s condition body value guardEvents middle r post bodyEvents restEvents}
      (guard : ExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun (decClockHOLFinite s) body none middle bodyEvents)
      (rest : StatementRun middle (.while condition body) r post restEvents) :
      StatementRun s (.while condition body) r post
        (.statement :: (guardEvents ++ bodyEvents ++ restEvents))
  | whileContinue {s condition body value guardEvents middle r post bodyEvents restEvents}
      (guard : ExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun (decClockHOLFinite s) body (some .continue) middle bodyEvents)
      (rest : StatementRun middle (.while condition body) r post restEvents) :
      StatementRun s (.while condition body) r post
        (.statement :: (guardEvents ++ bodyEvents ++ restEvents))
  | whileBreak {s condition body value guardEvents post bodyEvents}
      (guard : ExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun (decClockHOLFinite s) body (some .break) post bodyEvents) :
      StatementRun s (.while condition body) none post
        (.statement :: (guardEvents ++ bodyEvents))
  | whileTimeout {s condition body value guardEvents}
      (guard : ExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock = 0) :
      StatementRun s (.while condition body) (some .timeOut) (emptyLocalsHOLFinite s)
        (.statement :: guardEvents)
  | whileMissingGuard {s condition body guardEvents}
      (guard : ExpressionRun s condition none guardEvents) :
      StatementRun s (.while condition body) (some .error) s (.statement :: guardEvents)

  | whilePropagate {s condition body value guardEvents post bodyEvents result}
      (guard : ExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (notBreak : result ≠ .break) (notContinue : result ≠ .continue)
      (one : StatementRun (decClockHOLFinite s) body (some result) post bodyEvents) :
      StatementRun s (.while condition body) (some result) post
        (.statement :: (guardEvents ++ bodyEvents))

theorem StatementRun.sound {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) : evaluateHOLFiniteState s p = (r, post) := by
  induction run with
  | skip s => exact evaluateHOLFiniteState_skip s
  | seqNext one two ihOne ihTwo =>
    rw [evaluateHOLFiniteState_seq]
    dsimp only
    rw [fixClockHOLFinite_evaluateState, ihOne]
    exact ihTwo
  | @seqStop state first second result final left terminal one ih =>
    rw [evaluateHOLFiniteState_seq]
    dsimp only
    rw [fixClockHOLFinite_evaluateState, ih]
    cases result <;> simp_all
  | @iteYes state condition yes no value guardEvents result final bodyEvents guard nonzero body ih =>
    have evalGuard := guard.sound
    unfold expressionValue at evalGuard
    rw [evaluateHOLFiniteState_ite, evalGuard]
    have zero : value ≠ (0#64) := nonzero
    simpa [zero] using ih
  | iteNo guard body ih =>
    have evalGuard := guard.sound
    unfold expressionValue at evalGuard
    rw [evaluateHOLFiniteState_ite, evalGuard]
    simpa using ih

  | breakStmt s => exact evaluateHOLFiniteState_break s
  | continueStmt s => exact evaluateHOLFiniteState_continue s
  | whileFalse guard =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    simp only [evalHOLFinite_eq_toExact, hg]
    simp
  | whileNext guard nonzero clock one rest ihOne ihRest =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock, ihOne]
    exact ihRest
  | whileContinue guard nonzero clock one rest ihOne ihRest =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock, ihOne]
    exact ihRest
  | whileBreak guard nonzero clock one ihOne =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock, ihOne]
  | whileTimeout guard nonzero clock =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp [evalHOLFinite_eq_toExact, hg, nonzero, clock]
  | whileMissingGuard guard =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    simp only [evalHOLFinite_eq_toExact, hg]

  | whilePropagate guard nonzero clock notBreak notContinue one ihOne =>
    have hg := guard.sound
    unfold expressionValue at hg
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    change _ ≠ (0#64) at nonzero
    simp only [evalHOLFinite_eq_toExact, hg]
    simp [nonzero, clock, ihOne, notBreak, notContinue]

#print axioms StatementRun.sound
end InitECandidate.Runtime.FineCost
