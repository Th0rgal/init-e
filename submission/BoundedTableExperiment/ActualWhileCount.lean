import ActualWhileComposition

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Relational actual iteration count for a finite while run.  This relation is
NOT indexed by a proof certificate: it mirrors the actual states and events and
carries the count as a `Nat`. -/
inductive WhileCount {F : Type} (fn : MlS) (condition : ExpHOL 64)
    (body : ProgHOL 64) :
    PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List WorkEvent → Nat → Prop
  | stop {s} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition (some (.val (.word 0))) guardEvents) :
      WhileCount fn condition body s none s
        (.statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents) 0
  | next {s middle post} {value : BitVec 64} {r : Option (PanSemResultExact 64)}
      {guardEvents bodyEvents restEvents : List WorkEvent} {n : Nat}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun fn (decClockHOLFinite s) body none middle bodyEvents)
      (rest : WhileCount fn condition body middle r post restEvents n) :
      WhileCount fn condition body s r post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents ++ restEvents)) (n + 1)
  | breakLoop {s post} {value : BitVec 64}
      {guardEvents bodyEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0)
      (one : StatementRun fn (decClockHOLFinite s) body (some .break) post bodyEvents) :
      WhileCount fn condition body s none post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents)) 1
  | continueLoop {s middle post} {value : BitVec 64} {r : Option (PanSemResultExact 64)}
      {guardEvents bodyEvents restEvents : List WorkEvent} {n : Nat}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (one : StatementRun fn (decClockHOLFinite s) body (some .continue) middle bodyEvents)
      (rest : WhileCount fn condition body middle r post restEvents n) :
      WhileCount fn condition body s r post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents ++ restEvents)) (n + 1)
  | timeout {s} {value : BitVec 64} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock = 0) :
      WhileCount fn condition body s (some .timeOut) (emptyLocalsHOLFinite s)
        (.statement :: .cost (whileOverhead + loopMoves fn) :: guardEvents) 1
  | missingGuard {s} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition none guardEvents) :
      WhileCount fn condition body s (some .error) s
        (.statement :: guardEvents) 1
  | invalidGuard {s} {value : Option (ValueHOL 64)} {guardEvents : List WorkEvent}
      (guard : CostedExpressionRun s condition value guardEvents)
      (notWord : ∀ word : Word, value ≠ some (.val (.word word))) :
      WhileCount fn condition body s (some .error) s
        (.statement :: guardEvents) 1
  | propagate {s post} {value : BitVec 64}
      {guardEvents bodyEvents : List WorkEvent} {result : PanSemResultExact 64}
      (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
      (nonzero : value ≠ 0) (clock : s.clock ≠ 0)
      (notBreak : result ≠ .break) (notContinue : result ≠ .continue)
      (one : StatementRun fn (decClockHOLFinite s) body (some result) post bodyEvents) :
      WhileCount fn condition body s (some result) post
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents)) 1

/-- Every actual while certificate has some relational count. -/
theorem whileEvents_exists_count {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (cert : WhileEvents fn condition body s r post events) :
    ∃ n, WhileCount fn condition body s r post events n := by
  induction cert with
  | stop guard => exact ⟨0, WhileCount.stop guard⟩
  | next guard nonzero clock one rest ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, WhileCount.next guard nonzero clock one hn⟩
  | breakLoop guard nonzero one => exact ⟨1, WhileCount.breakLoop guard nonzero one⟩
  | continueLoop guard nonzero clock one rest ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, WhileCount.continueLoop guard nonzero clock one hn⟩
  | timeout guard nonzero clock => exact ⟨1, WhileCount.timeout guard nonzero clock⟩
  | missingGuard guard => exact ⟨1, WhileCount.missingGuard guard⟩
  | invalidGuard guard notWord => exact ⟨1, WhileCount.invalidGuard guard notWord⟩
  | propagate guard nonzero clock notBreak notContinue one =>
      exact ⟨1, WhileCount.propagate guard nonzero clock notBreak notContinue one⟩

/-- Actual relational count is bounded by the starting clock plus one. -/
theorem whileCount_le_clock {F : Type} {fn : MlS} {condition : ExpHOL 64}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    (count : WhileCount fn condition body s r post events n) :
    n ≤ s.clock + 1 := by
  induction count with
  | stop guard => omega
  | next guard nonzero clock one rest ih =>
      have hle := statementRun_clock_le one
      simp [decClockHOLFinite] at hle
      omega
  | breakLoop guard nonzero one => omega
  | continueLoop guard nonzero clock one rest ih =>
      have hle := statementRun_clock_le one
      simp [decClockHOLFinite] at hle
      omega
  | timeout guard nonzero clock => omega
  | missingGuard guard => omega
  | invalidGuard guard notWord => omega
  | propagate guard nonzero clock notBreak notContinue one => omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileEvents_exists_count
#print axioms BoundedTableExperiment.whileCount_le_clock
