import InitECandidate.Runtime.PanStatementWork

namespace BoundedTableExperiment

open InitECandidate.Runtime.FineCost
open Flapjack

/-- Event list emitted by the actual `StatementRun.storeValue` rule. -/
theorem storeValue_events {F : Type} {fn : Pancake.PanLang.MlS}
    {s : PanSemStateFiniteExact 64 F}
    {destination source : Pancake.PanLang.ExpHOL 64} {address : BitVec 64}
    {value : ValueHOL 64} {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination
      (some (ValueHOL.val (HolWordLab.word address))) addressEvents)
    (src : CostedExpressionRun s source (some value) valueEvents)
    (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
      (Classical.decPred _) s.memory = some mem) :
    StatementRun fn s (.store destination source) none { s with memory := mem }
      (.statement :: (addressEvents ++ valueEvents ++
        [.memory (flattenHOL value).length,
         .cost (storeOverhead (flattenHOL value).length)])) :=
  by
    classical
    exact StatementRun.storeValue dst src write

/-- A one-word path store is an actual `StatementRun` whose event list contains
exactly one memory access and the native one-word store overhead. -/
theorem path_store_one_word_events {F : Type} {fn : Pancake.PanLang.MlS}
    {s : PanSemStateFiniteExact 64 F}
    {destination source : Pancake.PanLang.ExpHOL 64} {address : BitVec 64}
    {value : ValueHOL 64} {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination
      (some (ValueHOL.val (HolWordLab.word address))) addressEvents)
    (src : CostedExpressionRun s source (some value) valueEvents)
    (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
      (Classical.decPred _) s.memory = some mem)
    (hword : (flattenHOL value).length = 1) :
    StatementRun fn s (.store destination source) none { s with memory := mem }
      (.statement :: (addressEvents ++ valueEvents ++
        [.memory (flattenHOL value).length,
         .cost (storeOverhead (flattenHOL value).length)])) ∧
    .memory 1 ∈ (.statement :: (addressEvents ++ valueEvents ++
        [.memory (flattenHOL value).length,
         .cost (storeOverhead (flattenHOL value).length)])) ∧
    .cost (storeOverhead 1) ∈ (.statement :: (addressEvents ++ valueEvents ++
        [.memory (flattenHOL value).length,
         .cost (storeOverhead (flattenHOL value).length)])) := by
  refine ⟨storeValue_events dst src write, ?_, ?_⟩
  · rw [hword]; simp
  · rw [hword]; simp

/-- Native units of one path-store memory event and its store overhead. -/
theorem path_store_one_word_units :
    (WorkEvent.memory 1).units.memoryAccesses = 1 ∧
    (WorkEvent.cost (storeOverhead 1)).units.nativeCost = storeOverhead 1 := by
  simp [WorkEvent.units]

/-- Every path-load or loop-guard expression has the actual expression run
with exactly one native-price event. -/
theorem path_load_expression_events {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : Pancake.PanLang.ExpHOL 64) :
    CostedExpressionRun s e (expressionValue s e) [.cost (sourcePrice s e)] :=
  costedExpressionRun_total s e

/-- The same expression run charges exactly `nativeCost * sourcePrice`. -/
theorem path_load_expression_cost {F : Type} (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (e : Pancake.PanLang.ExpHOL 64) :
    coeff.score (executionWork [.cost (sourcePrice s e)]) =
      coeff.nativeCost * sourcePrice s e := by
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]

/-- A path load expression's event list is nonempty and carries a native cost
event for its source price. -/
theorem path_load_has_cost_event {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : Pancake.PanLang.ExpHOL 64) :
    .cost (sourcePrice s e) ∈ (expressionEvents s e) := by
  simp [expressionEvents]

/-- Full score of the actual one-word path-store event trace: one statement
unit, both operand-expression runs, one memory access, and the one-word native
store overhead. -/
theorem path_store_one_word_score {F : Type} (coeff : Work)
    {fn : Pancake.PanLang.MlS} {s : PanSemStateFiniteExact 64 F}
    {destination source : Pancake.PanLang.ExpHOL 64} {address : BitVec 64}
    {value : ValueHOL 64} {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination
      (some (ValueHOL.val (HolWordLab.word address))) addressEvents)
    (src : CostedExpressionRun s source (some value) valueEvents)
    (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
      (Classical.decPred _) s.memory = some mem)
    (hword : (flattenHOL value).length = 1) :
    coeff.score (executionWork
        (WorkEvent.statement :: (addressEvents ++ valueEvents ++
          [WorkEvent.memory 1, WorkEvent.cost (storeOverhead 1)]))) =
      coeff.statements + coeff.score (executionWork addressEvents) +
      coeff.score (executionWork valueEvents) + coeff.memoryAccesses +
      coeff.nativeCost * storeOverhead 1 := by
  have _ := dst
  have _ := src
  have _ := write
  rw [executionWork_score_cons, executionWork_score_append,
    executionWork_score_append]
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.storeValue_events
#print axioms BoundedTableExperiment.path_store_one_word_events
#print axioms BoundedTableExperiment.path_load_expression_cost
#print axioms BoundedTableExperiment.path_store_one_word_score
