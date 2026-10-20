import InitECandidate.Runtime.PanAssignmentCallNormalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Normal actual assignment calls expose their real lookup and returned body. -/
theorem encode_header_normal_assignment_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name function : MlS) (arguments : List (ExpHOL 64))
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) function arguments)=(none,post)) :
 ∃values body callee shape value bodyPost,
 evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some values ∧
 lookupCodeHOLFinite s.code.lookup function values=some (body,callee,shape) ∧
 evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body=(some (.returned value),bodyPost) ∧
 post=setVarHOLFinite name value {bodyPost with locals:=s.locals} := by
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>rw [evaluateHOLFiniteState_call,args] at run;cases run
 | some values=>
  cases lookup : lookupCodeHOLFinite s.code.lookup function values with
  | none=>rw [evaluateHOLFiniteState_call,args] at run;simp only at run;rw [lookup] at run;cases run
  | some data=>
   obtain ⟨body,callee,shape⟩:=data
   obtain ⟨value,bodyPost,returned,postEq⟩:=assignment_call_normal_context s post .local name function arguments values body callee shape args lookup run
   exact ⟨values,body,callee,shape,value,bodyPost,rfl,lookup,returned,postEq⟩
#print axioms encode_header_normal_assignment_context
end InitECandidate.Runtime
