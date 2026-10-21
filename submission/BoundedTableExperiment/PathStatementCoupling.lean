import InitECandidate.Runtime.PanStatementWork

namespace BoundedTableExperiment

open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

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

/-- Concatenating path-slot event traces adds their scores. -/
theorem path_stores_score_append (coeff : Work) (left right : List WorkEvent) :
    coeff.score (executionWork (left ++ right)) =
      coeff.score (executionWork left) + coeff.score (executionWork right) :=
  executionWork_score_append coeff left right

/-- The score of a flat list of path-slot traces is the sum of their scores. -/
theorem path_stores_score (coeff : Work) (runs : List (List WorkEvent)) :
    coeff.score (executionWork runs.flatten) =
      (runs.map fun events => coeff.score (executionWork events)).sum := by
  induction runs with
  | nil => simp [executionWork, Work.score]
  | cons head tail ih =>
      simp [List.flatten_cons, path_stores_score_append, ih, List.sum_cons]

/-- One one-word path slot with no operand events. -/
def oneWordSlotEvents : List WorkEvent :=
  [.statement, .memory 1, .cost (storeOverhead 1)]

/-- `n` one-word path slots charge `n` times the per-slot statement, memory,
and native store-overhead work. -/
theorem n_path_slots_score (coeff : Work) :
    ∀ n, coeff.score (executionWork (List.flatten (List.replicate n oneWordSlotEvents))) =
      n * (coeff.statements + coeff.memoryAccesses +
        coeff.nativeCost * storeOverhead 1) := by
  intro n
  induction n with
  | zero => simp [executionWork, Work.score]
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, path_stores_score_append, ih]
      simp [oneWordSlotEvents, executionWork, WorkEvent.units, Work.plus, Work.score]
      rw [Nat.succ_mul]
      omega

/-- One executed `while` iteration of the candidate loop: the actual
`StatementRun.whileNext` rule with its statement, while overhead, guard
expression events, body events, and remaining loop events. -/
theorem whileNext_events {F : Type} {fn : Pancake.PanLang.MlS}
    {s : PanSemStateFiniteExact 64 F}
    {condition : Pancake.PanLang.ExpHOL 64} {body : Pancake.PanLang.ProgHOL 64} {value : Nat}
    {guardEvents : List WorkEvent} {middle : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {bodyEvents restEvents : List WorkEvent}
    (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
    (nonzero : (value : BitVec 64) ≠ 0) (clock : s.clock ≠ 0)
    (one : StatementRun fn (decClockHOLFinite s) body none middle bodyEvents)
    (rest : StatementRun fn middle (.while condition body) r post restEvents) :
    StatementRun fn s (.while condition body) r post
      (.statement :: .cost (whileOverhead + loopMoves fn) ::
        (guardEvents ++ bodyEvents ++ restEvents)) :=
  StatementRun.whileNext guard nonzero clock one rest

/-- Score of one actual `while` iteration decomposes into its statement unit,
while overhead, guard run, body run, and remaining loop. -/
theorem whileNext_score {F : Type} (coeff : Work) {fn : Pancake.PanLang.MlS}
    {s : PanSemStateFiniteExact 64 F}
    {condition : Pancake.PanLang.ExpHOL 64} {body : Pancake.PanLang.ProgHOL 64} {value : Nat}
    {guardEvents : List WorkEvent} {middle : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    {bodyEvents restEvents : List WorkEvent}
    (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
    (nonzero : (value : BitVec 64) ≠ 0) (clock : s.clock ≠ 0)
    (one : StatementRun fn (decClockHOLFinite s) body none middle bodyEvents)
    (rest : StatementRun fn middle (.while condition body) r post restEvents) :
    coeff.score (executionWork
        (.statement :: .cost (whileOverhead + loopMoves fn) ::
          (guardEvents ++ bodyEvents ++ restEvents))) =
      coeff.statements + coeff.nativeCost * (whileOverhead + loopMoves fn) +
      coeff.score (executionWork guardEvents) +
      coeff.score (executionWork bodyEvents) +
      coeff.score (executionWork restEvents) := by
  have _ := guard
  have _ := nonzero
  have _ := clock
  have _ := one
  have _ := rest
  rw [executionWork_score_cons, executionWork_score_cons,
    executionWork_score_append, executionWork_score_append]
  simp [WorkEvent.units, Work.score]
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.storeValue_events
#print axioms BoundedTableExperiment.path_store_one_word_events
#print axioms BoundedTableExperiment.path_load_expression_cost
#print axioms BoundedTableExperiment.path_store_one_word_score
#print axioms BoundedTableExperiment.n_path_slots_score
#print axioms BoundedTableExperiment.whileNext_score
