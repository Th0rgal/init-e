import InitECandidate.Runtime.PanCostTotal
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Source evaluation is deterministic independently of its recorded events. -/
theorem StatementRun.output_unique {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r r' : Option (PanSemResultExact 64)}
    {post post' : PanSemStateFiniteExact 64 F} {events events' : List WorkEvent}
    (one : StatementRun s p r post events) (two : StatementRun s p r' post' events') :
    (r, post) = (r', post') := one.sound.symm.trans two.sound

/-- Canonical executed event lists do not depend on a derivation witness,
including failed/timeout prefixes and the overlapping invalid-value rules. -/
theorem StatementRun.events_unique {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)}
    {post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (one : StatementRun s p r post events) :
    ∀ {r' post' events'}, StatementRun s p r' post' events' → events = events' := by
  classical
  induction one <;> intro r' post' events' other <;> cases other
  all_goals grind only [→ StatementRun.sound, → CostedExpressionRun.sound, → CostedExpressionRun.events_eq]

/-- The selected certified trace is the event list of ANY actual witness. -/
theorem sourceExecutionEvents_eq_of_run {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) : sourceExecutionEvents s p = events :=
  (sourceExecutionEvents_run s p).events_unique run

/-- Concrete helper/opcode trace prices are exactly the functional source
execution cost; no trace-choice hypothesis or quantitative oracle is needed. -/
theorem sourceExecutionCost_eq_of_run {F : Type} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) :
    sourceExecutionCost coeff s p = coeff.score (executionWork events) := by
  unfold sourceExecutionCost
  rw [sourceExecutionEvents_eq_of_run run]

/-- A bound on one concrete actual trace bounds the canonical functional cost. -/
theorem sourceExecutionCost_le_of_run {F : Type} (coeff : Work)
    {s post : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {bound : Nat}
    (run : StatementRun s p r post events)
    (price : coeff.score (executionWork events) ≤ bound) :
    sourceExecutionCost coeff s p ≤ bound := by
  rw [sourceExecutionCost_eq_of_run coeff run]
  exact price

#print axioms sourceExecutionEvents_eq_of_run
#print axioms sourceExecutionCost_eq_of_run
#print axioms sourceExecutionCost_le_of_run
#print axioms StatementRun.events_unique
#print axioms StatementRun.output_unique
end InitECandidate.Runtime.FineCost
