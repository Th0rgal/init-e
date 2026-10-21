import ActualWhileComposition

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Actual iteration-count relation for a while certificate.  The certificate
is an index, so this is a Prop and can be proved by induction on the actual
`StatementRun` while certificate. -/
inductive WhileIterations {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} :
    (s : PanSemStateFiniteExact 64 F) → Option (PanSemResultExact 64) →
    (post : PanSemStateFiniteExact 64 F) → (events : List WorkEvent) →
    WhileEvents fn condition body s r post events → Nat → Prop
  | stop {s} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents) :
      WhileIterations s none s
        (.statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents)
        (WhileEvents.stop (fn := fn) (condition := condition) (body := body) guard) 0
  | next {s middle post} {value : BitVec 64} {r : Option (PanSemResultExact 64)}
      {guardEvents bodyEvents restEvents : List WorkEvent} {n : Nat}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun fn (decClockHOLFinite s) body none middle bodyEvents)
      (rest : WhileEvents fn condition body middle r post restEvents)
      (tail : WhileIterations middle r post restEvents rest n) :
      WhileIterations s r post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents ++ restEvents))
        (WhileEvents.next (fn := fn) (condition := condition) (body := body)
          guard nonzero clock one rest) (n + 1)
  | breakLoop {s post} {value : BitVec 64}
      {guardEvents bodyEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0)
      (one : StatementRun fn (decClockHOLFinite s) body (some .break) post bodyEvents) :
      WhileIterations s none post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents))
        (WhileEvents.breakLoop (fn := fn) (condition := condition) (body := body)
          guard nonzero one) 1
  | continueLoop {s middle post} {value : BitVec 64} {r : Option (PanSemResultExact 64)}
      {guardEvents bodyEvents restEvents : List WorkEvent} {n : Nat}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun fn (decClockHOLFinite s) body (some .continue) middle bodyEvents)
      (rest : WhileEvents fn condition body middle r post restEvents)
      (tail : WhileIterations middle r post restEvents rest n) :
      WhileIterations s r post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents ++ restEvents))
        (WhileEvents.continueLoop (fn := fn) (condition := condition) (body := body)
          guard nonzero clock one rest) (n + 1)
  | timeout {s} {value : BitVec 64} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock = 0) :
      WhileIterations s (some .timeOut) (emptyLocalsHOLFinite s)
        (.statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents)
        (WhileEvents.timeout (fn := fn) (condition := condition) (body := body)
          guard nonzero clock) 1
  | missingGuard {s} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition none guardEvents) :
      WhileIterations s (some .error) s
        (.statement :: guardEvents)
        (WhileEvents.missingGuard (fn := fn) (condition := condition) (body := body) guard) 1
  | invalidGuard {s} {value : Option (ValueHOL 64)} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition value guardEvents)
      (notWord : ∀ word : Word, value ≠ some (.val (.word word))) :
      WhileIterations s (some .error) s
        (.statement :: guardEvents)
        (WhileEvents.invalidGuard (fn := fn) (condition := condition) (body := body)
          guard notWord) 1
  | propagate {s post} {value : BitVec 64}
      {guardEvents bodyEvents : List WorkEvent} {result : PanSemResultExact 64}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (notBreak : result ≠ .break) (notContinue : result ≠ .continue)
      (one : StatementRun fn (decClockHOLFinite s) body (some result) post bodyEvents) :
      WhileIterations s (some result) post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents))
        (WhileEvents.propagate (fn := fn) (condition := condition) (body := body)
          guard nonzero clock notBreak notContinue one) 1

end BoundedTableExperiment

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Every actual while certificate has a finite iteration count bounded by the
starting clock plus one. -/
theorem whileIterations_le_clock {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (cert : WhileEvents fn condition body s r post events) :
    ∃ n, WhileIterations s r post events cert n ∧ n ≤ s.clock + 1 := by
  induction cert with
  | stop guard =>
      exact ⟨0, WhileIterations.stop (fn := fn) (condition := condition)
        (body := body) guard, by omega⟩
  | next guard nonzero clock one rest ih =>
      obtain ⟨n, hn, hb⟩ := ih
      refine ⟨n + 1, WhileIterations.next (fn := fn) (condition := condition)
        (body := body) guard nonzero clock one rest hn, ?_⟩
      have hle := statementRun_clock_le one
      simp [decClockHOLFinite] at hle
      omega
  | breakLoop guard nonzero one =>
      exact ⟨1, WhileIterations.breakLoop (fn := fn) (condition := condition)
        (body := body) guard nonzero one, by omega⟩
  | continueLoop guard nonzero clock one rest ih =>
      obtain ⟨n, hn, hb⟩ := ih
      refine ⟨n + 1, WhileIterations.continueLoop (fn := fn) (condition := condition)
        (body := body) guard nonzero clock one rest hn, ?_⟩
      have hle := statementRun_clock_le one
      simp [decClockHOLFinite] at hle
      omega
  | timeout guard nonzero clock =>
      exact ⟨1, WhileIterations.timeout (fn := fn) (condition := condition)
        (body := body) guard nonzero clock, by omega⟩
  | missingGuard guard =>
      exact ⟨1, WhileIterations.missingGuard (fn := fn) (condition := condition)
        (body := body) guard, by omega⟩
  | invalidGuard guard notWord =>
      exact ⟨1, WhileIterations.invalidGuard (fn := fn) (condition := condition)
        (body := body) guard notWord, by omega⟩
  | propagate guard nonzero clock notBreak notContinue one =>
      exact ⟨1, WhileIterations.propagate (fn := fn) (condition := condition)
        (body := body) guard nonzero clock notBreak notContinue one, by omega⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileIterations_le_clock
