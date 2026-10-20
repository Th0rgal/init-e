import InitECandidate.Runtime.ReturnedStorePlanMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- Concrete scalar stores preceding an arbitrary real continuation. -/
inductive BoundReturnedStorePrefix {F : Type} (bindings : HolFiniteMapExact MlS (ValueHOL 64)) :
 ProgHOL 64→ProgHOL 64→List (BitVec 64×BitVec 64)→Prop
 | finish (tail : ProgHOL 64) : BoundReturnedStorePrefix (F:=F) bindings tail tail []
 | store (destination expression : ExpHOL 64) (address value : BitVec 64)
   (addressEval : ∀s : PanSemStateFiniteExact 64 F,s.locals=bindings→
    @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word address)))
   (valueEval : ∀s : PanSemStateFiniteExact 64 F,s.locals=bindings→
    @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word value)))
   {rest tail : ProgHOL 64} {plan : List (BitVec 64×BitVec 64)}
   (next : BoundReturnedStorePrefix (F:=F) bindings rest tail plan) :
   BoundReturnedStorePrefix (F:=F) bindings (.seq (.store destination expression) rest) tail ((address,value)::plan)

/-- A returned original prefix forces each real store to complete normally;
its exact continuation therefore runs from the concrete ordered write state.
No mapped-address or successful-store premise is supplied. -/
theorem evaluate_bound_returned_store_prefix {F : Type}
 {bindings : HolFiniteMapExact MlS (ValueHOL 64)} {program tail : ProgHOL 64} {plan : List (BitVec 64×BitVec 64)}
 (supported : BoundReturnedStorePrefix (F:=F) bindings program tail plan)
 (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) (locals : s.locals=bindings)
 (run : evaluateHOLFiniteState s program=(some (.returned value),post)) :
 evaluateHOLFiniteState {s with memory:=storePlanMemory s.memory plan} tail=(some (.returned value),post) := by
 induction supported generalizing s with
 | finish tail=>simpa [storePlanMemory] using run
 | store destination expression address word addressEval valueEval next ih=>
  obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first
   (by intro v;exact evaluate_noDirectReturn _ rfl s v) run
  have same:=store_normal_exact s middle destination expression address word (addressEval s locals) (valueEval s locals) normal
  subst middle
  have actual:=ih (sourceWriteWord s address word) locals tailRun
  simpa [storePlanMemory,List.foldl,sourceWriteWord] using actual
#print axioms evaluate_bound_returned_store_prefix
end InitECandidate.Runtime
