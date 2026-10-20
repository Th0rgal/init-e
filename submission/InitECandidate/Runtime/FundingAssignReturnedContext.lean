import InitECandidate.Runtime.FundingAllocationReturnedContext
import InitECandidate.Runtime.ReturnedStorePlanMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A real successful assignment has the exact source update. Its validity
check is obtained from execution instead of supplied as a new premise. -/
theorem funding_assignment_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (kind : VarKind) (name : MlS) (expression : ExpHOL 64) (word : BitVec 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.assign kind name expression) tail)=(some (.returned value),post)) :
 evaluateHOLFiniteState (setKvarHOLFinite kind name (.val (.word word)) s) tail=(some (.returned value),post) := by
 obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) s v) run
 rw [evaluateHOLFiniteState_assign,evaluated] at normal
 dsimp only at normal
 split at normal
 · have same : middle=setKvarHOLFinite kind name (.val (.word word)) s:=(Prod.mk.inj normal).2.symm
   subst middle
   exact tailRun
 · simp at normal
theorem funding_store_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (destination expression : ExpHOL 64) (address word : BitVec 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (addressEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word address)))
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.store destination expression) tail)=(some (.returned value),post)) :
 evaluateHOLFiniteState (sourceWriteWord s address word) tail=(some (.returned value),post) := by
 obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) s v) run
 have middleEq:=store_normal_exact s middle destination expression address word addressEval evaluated normal
 subst middle
 exact tailRun
#print axioms funding_assignment_returned_context
#print axioms funding_store_returned_context
end InitECandidate.Runtime
