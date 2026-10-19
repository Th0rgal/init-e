import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.DecodeStepLeafReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

noncomputable def storePlanMemory (memory : BitVec 64 → HolWordLab 64)
    (plan : List (BitVec 64 × BitVec 64)) : BitVec 64 → HolWordLab 64 :=
  plan.foldl (fun memory entry current => if current=entry.1 then .word entry.2 else memory current) memory

inductive BoundReturnedStorePlan {F : Type} (bindings : HolFiniteMapExact MlS (ValueHOL 64)) :
    ProgHOL 64 → List (BitVec 64 × BitVec 64) → Prop
  | finish (tail : ProgHOL 64) (readOnly : readOnlyMemory tail = true) :
      BoundReturnedStorePlan (F := F) bindings tail []
  | store (destination expression : ExpHOL 64) (address value : BitVec 64)
      (addressEval : ∀ s : PanSemStateFiniteExact 64 F, s.locals = bindings →
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination = some (.val (.word address)))
      (valueEval : ∀ s : PanSemStateFiniteExact 64 F, s.locals = bindings →
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression = some (.val (.word value)))
      {tail : ProgHOL 64} {plan : List (BitVec 64 × BitVec 64)}
      (rest : BoundReturnedStorePlan (F := F) bindings tail plan) :
      BoundReturnedStorePlan (F := F) bindings (.seq (.store destination expression) tail) ((address,value)::plan)

theorem store_normal_exact {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address value : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression = some (.val (.word value)))
    (run : evaluateHOLFiniteState s (.store destination expression) = (none,post)) :
    post = sourceWriteWord s address value := by
  by_cases accessible : s.memaddrs address
  · exact (Prod.mk.inj ((evaluate_store_word s address value destination expression addressEval valueEval accessible).symm.trans run)).2.symm
  · rw [evaluateHOLFiniteState_store,addressEval,valueEval] at run
    simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at run

theorem evaluate_bound_returned_store_plan_memory {F : Type}
    {bindings : HolFiniteMapExact MlS (ValueHOL 64)} {program : ProgHOL 64} {plan : List (BitVec 64 × BitVec 64)}
    (supported : BoundReturnedStorePlan (F := F) bindings program plan)
    (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) (locals : s.locals = bindings)
    (run : evaluateHOLFiniteState s program = (some (.returned value),post)) :
    post.memory = storePlanMemory s.memory plan := by
  induction supported generalizing s post with
  | finish tail readOnly =>
    have frame := evaluate_readOnly_memory tail readOnly s
    rw [run] at frame
    exact frame
  | store destination expression address word addressEval valueEval rest ih =>
    obtain ⟨middle,normal,tailRun⟩ := seq_returned_of_nonreturning_first
      (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
    have same := store_normal_exact s middle destination expression address word (addressEval s locals) (valueEval s locals) normal
    subst middle
    have result := ih (sourceWriteWord s address word) post locals tailRun
    simpa [storePlanMemory,List.foldl,Function.update,sourceWriteWord] using result

#print axioms store_normal_exact
#print axioms evaluate_bound_returned_store_plan_memory
end InitECandidate.Runtime
