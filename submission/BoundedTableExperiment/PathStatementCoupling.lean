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

end BoundedTableExperiment

#print axioms BoundedTableExperiment.storeValue_events
#print axioms BoundedTableExperiment.path_store_one_word_events
