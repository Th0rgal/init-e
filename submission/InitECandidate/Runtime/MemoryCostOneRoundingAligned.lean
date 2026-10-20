import InitECandidate.Runtime.MemoryCostOneAlignedTail
import InitECandidate.Runtime.MemoryCeil32DeclarationGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual before/after ceil32 calls imply aligned returned expansion when
current memory length is aligned; saturation exits return zero expansion. -/
theorem memory_cost_one_rounding_aligned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (current endpoint : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.locals.lookup (ofString "cur")=some (.val (.word current)))
 (atEndpoint : s.locals.lookup (ofString "endp")=some (.val (.word endpoint)))
 (aligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 7)=(some (.returned value),post)) :
 MemoryExpansionAligned value := by
 rw [source_memory_cost_one_7] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "cur")]=some [.val (.word current)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atCurrent]
 obtain ⟨before,firstPost,firstOutput,firstRun,firstScope,_,_,fixed,_,_,firstCode,_,_⟩:=memory_ceil32_declaration_geometry s post (ofString "before") _ (memoryCostOneAt 8) current value args code run
 have beforeAligned : before.toNat%32=0 := by rw [fixed aligned];exact aligned
 let first:=setVarHOLFinite (ofString "before") (.val (.word before)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 8)=_ at firstRun
 have endpointAt : first.locals.lookup (ofString "endp")=some (.val (.word endpoint)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atEndpoint
 have afterArgs : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a)) [.var .local (ofString "endp")]=some [.val (.word endpoint)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,endpointAt]
 rw [source_memory_cost_one_8] at firstRun
 obtain ⟨after,secondPost,secondOutput,secondRun,secondScope,_,afterAligned,_,_,_,secondCode,_,_⟩:=memory_ceil32_declaration_geometry first firstOutput (ofString "after") _ (memoryCostOneAt 9) endpoint value afterArgs (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "after") (.val (.word after)) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 9)=_ at secondRun
 apply memory_cost_one_guarded_aligned second secondOutput before after value _ _ beforeAligned afterAligned (secondCode.trans (firstCode.trans code)) secondRun
 · simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Actual length load preserves its previously calculated real endpoint. -/
theorem memory_cost_one_loaded_aligned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current endpoint : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atEndpoint : s.locals.lookup (ofString "endp")=some (.val (.word endpoint)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (aligned : current.toNat%32=0) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 6)=(some (.returned value),post)) :
 MemoryExpansionAligned value := by
 rw [source_memory_cost_one_6] at run
 obtain ⟨loaded,output,evaluated,nextRun,scope⟩:=funding_declaration_returned_context run
 have evalCurrent:=eval_fundingLoad s frame (32#64) current atFrame domain currentAt
 have equal : loaded=.val (.word current):=Option.some.inj (evaluated.symm.trans evalCurrent)
 subst loaded
 apply memory_cost_one_rounding_aligned (setVarHOLFinite (ofString "cur") (.val (.word current)) s) output current endpoint value _ _ aligned code nextRun
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atEndpoint
#print axioms memory_cost_one_rounding_aligned
#print axioms memory_cost_one_loaded_aligned
end InitECandidate.Runtime
