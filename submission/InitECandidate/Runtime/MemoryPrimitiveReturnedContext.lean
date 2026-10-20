import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual primitive assignment validity is obtained from the normal prefix
of the returned source sequence. -/
theorem memory_primitive_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
 (result value : ValueHOL 64) (tail : ProgHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values)
 (primitive : panPrimopHOLExact operator values=some result)
 (run : evaluateHOLFiniteState s (.seq (.primitive name operator arguments) tail)=(some (.returned value),post)) :
 evaluateHOLFiniteState (setVarHOLFinite name result s) tail=(some (.returned value),post) := by
 have argsExact : @evalListHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values := args
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_primitive,argsExact] at run
 dsimp only at run
 rw [primitive] at run
 dsimp only at run
 by_cases valid : isValidValueHOLFinite s .local name result=true
 · rw [if_pos valid] at run;exact run
 · rw [if_neg valid] at run;cases run

#print axioms memory_primitive_returned_context
end InitECandidate.Runtime
