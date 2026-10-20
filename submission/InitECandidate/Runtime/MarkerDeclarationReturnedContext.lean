import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- A concrete installed marker whose original body returns a global exposes
its actual continuation at the one-tick caller clock, with no success/fuel
premise beyond this same returned declaration execution. -/
theorem marker_declaration_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name function global : MlS) (body tail : ProgHOL 64) (pointer : BitVec 64) (value : ValueHOL 64)
 (installed : s.code.lookup function=some ([],body,.one))
 (source : body=.return (.var .global global))
 (atPointer : s.globals.lookup global=some (.val (.word pointer)))
 (run : evaluateHOLFiniteState s (.decCall name .one function [] tail)=(some (.returned value),post)) :
 ∃output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) {s with clock:=s.clock-1}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 have lookup:=pan_no_args_lookup s.code.lookup function body installed
 obtain ⟨returned,bodyPost,output,bodyRun,shape,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name function .one .one
  [] [] body tail HolFiniteMapExact.empty value rfl lookup run
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have exactBody : evaluateHOLFiniteState entry body=
  (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite entry) := by
  rw [source]
  simp [evaluateHOLFiniteState_return,evalHOLExact,show entry.globals.lookup global=some (.val (.word pointer)) from atPointer,shapeOfHOLExact]
 obtain ⟨returnedEq,bodyPostEq⟩:=Prod.mk.inj (bodyRun.symm.trans exactBody)
 have valueEq:=PanSemResultExact.returned.inj (Option.some.inj returnedEq)
 rw [valueEq,bodyPostEq] at tailRun
 refine ⟨output,?_,postEq⟩
 simpa only [entry,callEntryStateHOLFinite,emptyLocalsHOLFinite] using tailRun
#print axioms marker_declaration_returned_context
end InitECandidate.Runtime
