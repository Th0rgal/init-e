import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.PanReturnedPath
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Expose the real successful declaration call and exact caller-local resume,
with no assumed argument values or callee execution. -/
theorem encode_header_returned_declaration_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (.decCall name shape function arguments tail)=(some (.returned value),post)) :
 ∃values body callee returnShape returned bodyPost ready output,
 evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values ∧
 lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape) ∧
 evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.returned returned),bodyPost) ∧
 ready.locals=s.locals ∧ready.memory=bodyPost.memory ∧ready.globals=bodyPost.globals ∧ready.clock=bodyPost.clock ∧
 ready.memaddrs=bodyPost.memaddrs ∧ready.be=bodyPost.be ∧ready.code=bodyPost.code ∧
 evaluateHOLFiniteState (setVarHOLFinite name returned ready) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 obtain ⟨values,body,callee,returnShape,_,_,args,lookup,_⟩:=decCall_returned run
 obtain ⟨returned,bodyPost,ready,output,bodyRun,locals,memory,globals,clock,domain,endian,code,tailRun,postEq⟩:=
  evaluate_decCall_returned_global_memory_clock_scope s post name function shape returnShape arguments values body tail callee value args lookup run
 exact ⟨values,body,callee,returnShape,returned,bodyPost,ready,output,args,lookup,bodyRun,locals,memory,globals,clock,domain,endian,code,tailRun,postEq⟩
#print axioms encode_header_returned_declaration_context
end InitECandidate.Runtime
