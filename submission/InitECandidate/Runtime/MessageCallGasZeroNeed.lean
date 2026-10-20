import InitECandidate.Runtime.MessageCallGasArithmeticTail
import InitECandidate.Runtime.AddSat
import InitECandidate.Runtime.VmFn_add_sat
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem add_sat_zero_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word (0#64)),.val (.word (0#64))])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "add_sat") arguments tail)=(some (.returned value),post)) :
 ∃output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word 0)) {s with clock:=s.clock-1}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 have installed : s.code.lookup (ofString "add_sat")=some addSatCodeEntry := by rw [code];exact vmLookup_add_sat
 by_cases clock : s.clock=0
 · rw [evaluateHOLFiniteState_decCall_total,args] at run
   dsimp only at run
   rw [lookup_source_addSat s.code.lookup (0#64) (0#64) installed] at run
   simp [clock] at run
 · rw [evaluate_addSat_decCall s name arguments tail (0#64) (0#64) installed args clock] at run
   have satZero : wordAddSat (0#64) (0#64)=0:=by decide_cbv
   rw [satZero] at run
   let ready:=setVarHOLFinite name (.val (.word (0#64))) {s with clock:=s.clock-1}
   change (let output:=evaluateHOLFiniteState ready tail;(output.1,{output.2 with locals:=HolFiniteMapExact.resVarEq output.2.locals (name,s.locals.lookup name)}))=_ at run
   cases tailRun : evaluateHOLFiniteState ready tail with
   | mk result output=>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩:=Prod.mk.inj run
    change result=some (.returned value) at resultEq
    subst result
    exact ⟨output,rfl,postEq.symm⟩

/-- The actual need call with zero memory/extra costs and its real unsigned
failure guard always continue to the allocation arithmetic. -/
theorem message_call_gas_zero_need_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (remaining : BitVec 64) (value : ValueHOL 64)
 (atRemaining : s.locals.lookup (ofString "gas_left")=some (.val (.word remaining)))
 (atMemory : s.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))))
 (atExtra : s.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (messageCallGasAt 3)=(some (.returned value),post)) :
 ∃output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite (ofString "need") (.val (.word 0)) {s with clock:=s.clock-1}) (messageCallGasAt 5)=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (ofString "need",s.locals.lookup (ofString "need"))} := by
 have source3 : messageCallGasAt 3=.decCall (ofString "need") .one (ofString "add_sat") [.var .local (ofString "extra_gas"),.var .local (ofString "memory_cost")] (messageCallGasAt 4):=rfl
 have source4 : messageCallGasAt 4=.seq (.ite (.cmp .lower (.var .local (ofString "gas_left")) (.var .local (ofString "need")))
  (match messageCallGasAt 4 with | .seq (.ite _ branch _) _=>branch | _=>.skip) .skip) (messageCallGasAt 5):=by rfl
 rw [source3] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "extra_gas"),.var .local (ofString "memory_cost")]=some [.val (.word (0#64)),.val (.word (0#64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atExtra,atMemory]
 obtain ⟨output,tailRun,postEq⟩:=add_sat_zero_returned_context s post (ofString "need") _ (messageCallGasAt 4) value args code run
 let ready:=setVarHOLFinite (ofString "need") (.val (.word (0#64))) {s with clock:=s.clock-1}
 change evaluateHOLFiniteState ready (messageCallGasAt 4)=_ at tailRun
 have condition : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
  (.cmp .lower (.var .local (ofString "gas_left")) (.var .local (ofString "need")))=some (.val (.word 0)) := by
  simp (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,atRemaining,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
 rw [source4,evaluateHOLFiniteState_seq] at tailRun
 rw [evaluateHOLFiniteState_ite,condition] at tailRun
 refine ⟨output,?_,postEq⟩
 simpa [evaluateHOLFiniteState_skip,fixClockHOLFinite] using tailRun
#print axioms add_sat_zero_returned_context
#print axioms message_call_gas_zero_need_returned_context
end InitECandidate.Runtime
