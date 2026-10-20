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

#print axioms StatementRun.sound
end InitECandidate.Runtime.FineCost
