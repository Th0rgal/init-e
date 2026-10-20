import InitECandidate.Runtime.PanCostCompleteness
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

private theorem cost_measure_decrease {oldClock newClock oldSize newSize : Nat}
    (clock : newClock ≤ oldClock) (size : newSize < oldSize) :
    Prod.Lex Nat.lt Nat.lt (newClock, newSize) (oldClock, oldSize) := by
  by_cases strict : newClock < oldClock
  · apply Prod.Lex.left; exact strict
  · have equal : newClock = oldClock := by omega
    subst newClock
    apply Prod.Lex.right; exact size

/-- Global source-cost completeness. Calls and loop iterations decrease the
semantic clock; structural composition decreases the program size. No guest
well-formedness or accepting-result hypothesis is required. -/
theorem source_statement_cost_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) : HasStatementCost s p := by
  classical
  cases p with
  | seq first second =>
    apply sequence_cost_complete s first second
    · exact source_statement_cost_complete s first
    · intro post run
      have mono := evaluateHOLFiniteState_clock_le s first
      rw [run] at mono
      simp only [] at mono
      exact source_statement_cost_complete post second
  | ite condition yes no =>
    apply conditional_cost_complete s condition yes no
    intro word guard
    by_cases zero : word = 0
    · simp only [zero, ↓reduceIte]
      exact source_statement_cost_complete s no
    · simp only [zero, ↓reduceIte]
      exact source_statement_cost_complete s yes
  | dec name shape initializer body =>
    apply declaration_cost_complete s name shape initializer body
    intro value evaluated matched
    exact source_statement_cost_complete (setVarHOLFinite name value s) body
  | «while» condition body =>
    apply while_cost_complete s condition body
    · intro word guard nonzero clock
      have smaller : (decClockHOLFinite s).clock < s.clock := by
        simp only [decClockHOLFinite]; omega
      exact source_statement_cost_complete (decClockHOLFinite s) body
    · intro clock post run
      have mono := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
      rw [run] at mono
      have smaller : post.clock < s.clock := by
        simp only [decClockHOLFinite] at mono; omega
      exact source_statement_cost_complete post (.while condition body)
    · intro clock post run
      have mono := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
      rw [run] at mono
      have smaller : post.clock < s.clock := by
        simp only [decClockHOLFinite] at mono; omega
      exact source_statement_cost_complete post (.while condition body)
  | call info function arguments =>
    apply call_cost_complete s info function arguments
    · intro values body callee returnShape args lookup clock
      have smaller : (callEntryStateHOLFinite s callee).clock < s.clock := by
        simp only [callEntryStateHOLFinite]; omega
      exact source_statement_cost_complete (callEntryStateHOLFinite s callee) body
    · intro callee body returnShape result post entry program clock run plan
      have mono := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
      rw [run] at mono
      have handlerClock := callCostPlan_handler_clock s post entry info returnShape result program plan
      have smaller : entry.clock < s.clock := by
        simp only [callEntryStateHOLFinite] at mono; omega
      exact source_statement_cost_complete entry program
  | decCall name shape function arguments continuation =>
    apply declared_call_cost_complete s name shape function arguments continuation
    · intro values body callee returnShape args lookup clock
      have smaller : (callEntryStateHOLFinite s callee).clock < s.clock := by
        simp only [callEntryStateHOLFinite]; omega
      exact source_statement_cost_complete (callEntryStateHOLFinite s callee) body
    · intro callee body value post clock run
      have mono := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
      rw [run] at mono
      have smaller : (setVarHOLFinite name value { post with locals := s.locals }).clock < s.clock := by
        simp only [callEntryStateHOLFinite] at mono
        simp only [setVarHOLFinite]
        omega
      exact source_statement_cost_complete
        (setVarHOLFinite name value { post with locals := s.locals }) continuation
  | _ => exact atomic_statement_cost_complete s _ rfl
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply cost_measure_decrease <;> simp_all [setVarHOLFinite] <;> omega)
    | omega

/-- Every exact source evaluation has a finite, size-aware work trace. -/
theorem source_evaluation_cost_trace {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) :
    ∃ events, StatementRun s p (evaluateHOLFiniteState s p).1
      (evaluateHOLFiniteState s p).2 events :=
  (source_statement_cost_complete s p).exact_trace

/-- Select a certified finite source trace. Compiler and guest bounds should
hold for all StatementRun traces, hence also for this selected witness. -/
noncomputable def sourceExecutionEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) : List WorkEvent := (source_evaluation_cost_trace s p).choose

theorem sourceExecutionEvents_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) :
    StatementRun s p (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2
      (sourceExecutionEvents s p) := (source_evaluation_cost_trace s p).choose_spec

/-- Finite source execution cost, parameterized by compiler-certified unit
coefficients. It is independent of any whole-program syntax maximum. -/
noncomputable def sourceExecutionCost {F : Type} (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Nat :=
  coeff.score (executionWork (sourceExecutionEvents s p))

theorem sourceExecutionCost_spec {F : Type} (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    ∃ events, StatementRun s p (evaluateHOLFiniteState s p).1
      (evaluateHOLFiniteState s p).2 events ∧
      sourceExecutionCost coeff s p = coeff.score (executionWork events) :=
  ⟨sourceExecutionEvents s p, sourceExecutionEvents_run s p, rfl⟩

#print axioms sourceExecutionCost_spec

#print axioms source_statement_cost_complete
#print axioms source_evaluation_cost_trace
end InitECandidate.Runtime.FineCost
