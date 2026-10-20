import InitECandidate.Runtime.AddSat
import InitECandidate.Runtime.VmFn_add_sat
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Exact real saturating-add declaration continuation, including actual call
clock and original lexical scope. No callee execution premise. -/
theorem add_sat_returned_exact_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (left right : BitVec 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word left),.val (.word right)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "add_sat") arguments tail)=(some (.returned value),post)) :
 ∃output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (wordAddSat left right))) {s with clock:=s.clock-1}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 have installed : s.code.lookup (ofString "add_sat")=some addSatCodeEntry := by rw [code];exact vmLookup_add_sat
 by_cases clock : s.clock=0
 · rw [evaluateHOLFiniteState_decCall_total,args] at run
   dsimp only at run
   rw [lookup_source_addSat s.code.lookup left right installed] at run
   simp [clock] at run
 · rw [evaluate_addSat_decCall s name arguments tail left right installed args clock] at run
   let ready:=setVarHOLFinite name (.val (.word (wordAddSat left right))) {s with clock:=s.clock-1}
   change (let output:=evaluateHOLFiniteState ready tail;(output.1,{output.2 with locals:=HolFiniteMapExact.resVarEq output.2.locals (name,s.locals.lookup name)}))=_ at run
   cases tailRun : evaluateHOLFiniteState ready tail with
   | mk result output=>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩:=Prod.mk.inj run
    change result=some (.returned value) at resultEq
    subst result
    exact ⟨output,rfl,postEq.symm⟩

#print axioms add_sat_returned_exact_context
end InitECandidate.Runtime
