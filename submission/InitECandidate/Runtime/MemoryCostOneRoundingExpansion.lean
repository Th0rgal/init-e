import InitECandidate.Runtime.MemoryCostOneTailExpansion
import InitECandidate.Runtime.MemoryCeil32DeclarationReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Both actual rounding calls and the complete original arithmetic suffix.
The before call's upward rounding, not an assumed callee result, bounds the
real returned expansion at every current length. -/
theorem memory_cost_one_rounding_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (current : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.locals.lookup (ofString "cur")=some (.val (.word current)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 7)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 rw [source_memory_cost_one_7] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "cur")]=some [.val (.word current)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atCurrent]
 obtain ⟨before,firstPost,firstOutput,firstRun,firstScope,beforeAbove,_,_,firstCode,_,_⟩:=
  memory_ceil32_declaration_returned s post (ofString "before") _ (memoryCostOneAt 8) current value args code run
 let first:=setVarHOLFinite (ofString "before") (.val (.word before)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 8)=_ at firstRun
 rw [source_memory_cost_one_8] at firstRun
 obtain ⟨after,secondPost,secondOutput,secondRun,secondScope,_,_,secondCode,_,_⟩:=
  memory_cost_pure_declaration_returned first firstOutput (ofString "after") (ofString "ceil32") _ (memoryCostOneAt 9) value (firstCode.trans code) (by decide) (by decide) firstRun
 let second:=setVarHOLFinite (ofString "after") (.val (.word after)) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 9)=_ at secondRun
 apply memory_cost_one_guarded_expansion second secondOutput current before after value _ _ beforeAbove (secondCode.trans (firstCode.trans code)) secondRun
 · simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- The actual current-length load precedes those rounding calls. -/
theorem memory_cost_one_loaded_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 6)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 rw [source_memory_cost_one_6] at run
 obtain ⟨loaded,output,evaluated,nextRun,scope⟩:=funding_declaration_returned_context run
 have evalCurrent:=eval_fundingLoad s frame (32#64) current atFrame domain currentAt
 have equal : loaded=.val (.word current):=Option.some.inj (evaluated.symm.trans evalCurrent)
 subst loaded
 apply memory_cost_one_rounding_expansion (setVarHOLFinite (ofString "cur") (.val (.word current)) s) output current value _ code nextRun
 simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
#print axioms memory_cost_one_rounding_expansion
#print axioms memory_cost_one_loaded_expansion
end InitECandidate.Runtime
