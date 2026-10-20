import InitECandidate.Runtime.FrameMemoryAllocationSource
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.TrapCallTerminal
import InitECandidate.Runtime.HtabInsertRawFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact scope endpoint of an ordinary declaration on an actual returned run. -/
theorem funding_declaration_returned_context {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {name : MlS} {shape : ShapeHOL} {initializer : ExpHOL 64} {body : ProgHOL 64} {v : ValueHOL 64}
 (run : evaluateHOLFiniteState s (.dec name shape initializer body)=(some (.returned v),post)) :
 ∃value inner, @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) initializer=some value ∧
 evaluateHOLFiniteState (setVarHOLFinite name value s) body=(some (.returned v),inner) ∧
 post={inner with locals:=HolFiniteMapExact.resVarEq inner.locals (name,s.locals.lookup name)} := by
 rw [evaluateHOLFiniteState_dec_total] at run
 dsimp only at run
 split at run
 · simp at run
 · rename_i value evaluated
   split at run
   · cases innerRun : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
     | mk result inner=>
       rw [innerRun] at run
       obtain ⟨resultEq,postEq⟩:=Prod.mk.inj run
       change result=some (.returned v) at resultEq
       subst post
       exact ⟨value,inner,evaluated,by rw [innerRun,resultEq],rfl⟩
   · simp at run

/-- A normal trap-guard prefix must take its real zero/skip branch. -/
theorem funding_trap_guard_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (flag : BitVec 64) (code : s.code=originalRuntimeCode)
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word flag)))
 (run : evaluateHOLFiniteState s (.ite condition (.call (some (none,none)) (ofString "trap_with") [.const 6]) .skip)=(none,post)) :
 flag=0 ∧post=s := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const 6]=some [.val (.word (6#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
 rw [evaluateHOLFiniteState_ite,evaluated] at run
 by_cases zero : flag=0
 · subst flag
   constructor
   · rfl
   · have eq : s=post := by simpa [evaluateHOLFiniteState_skip] using run
     exact eq.symm
 · have bad:=evaluate_trap_call_terminal s (.const 6) 6 code args
   simp only [zero,if_false] at run
   exact False.elim (bad (by rw [run]))

#print axioms funding_declaration_returned_context
#print axioms funding_trap_guard_normal
end InitECandidate.Runtime
