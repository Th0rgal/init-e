import InitECandidate.Runtime.MemoryCostOneSizeTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem memory_cost_one_rounding_size {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 7)=(some (.returned value),post)) :
 MemoryExpansionSizeBound (2^37) value := by
 rw [source_memory_cost_one_7] at run
 obtain ⟨before,firstPost,firstOutput,firstRun,firstScope,_,_,firstCode,_,_⟩:=
  memory_cost_pure_declaration_returned s post (ofString "before") (ofString "ceil32") _ (memoryCostOneAt 8) value code (by decide) (by decide) run
 let first:=setVarHOLFinite (ofString "before") (.val (.word before)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 8)=_ at firstRun
 rw [source_memory_cost_one_8] at firstRun
 obtain ⟨after,secondPost,secondOutput,secondRun,secondScope,_,_,secondCode,_,_⟩:=
  memory_cost_pure_declaration_returned first firstOutput (ofString "after") (ofString "ceil32") _ (memoryCostOneAt 9) value (firstCode.trans code) (by decide) (by decide) firstRun
 let second:=setVarHOLFinite (ofString "after") (.val (.word after)) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 9)=_ at secondRun
 apply memory_cost_one_guarded_size second secondOutput before after value _ _ (secondCode.trans (firstCode.trans code)) secondRun
 · simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem memory_cost_one_loaded_size {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 6)=(some (.returned value),post)) :
 MemoryExpansionSizeBound (2^37) value := by
 rw [source_memory_cost_one_6] at run
 obtain ⟨loaded,output,_,nextRun,_⟩:=funding_declaration_returned_context run
 exact memory_cost_one_rounding_size (setVarHOLFinite (ofString "cur") loaded s) output value code nextRun

theorem memory_cost_one_preparation_size {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 2)=(some (.returned value),post)) :
 MemoryExpansionSizeBound (2^37) value := by
 rw [source_memory_cost_one_2] at run
 obtain ⟨start,firstPost,firstOutput,firstRun,firstScope,_,_,firstCode,_,_⟩:=
  memory_cost_pure_declaration_returned s post (ofString "s") (ofString "sat_word") _ (memoryCostOneAt 3) value code (by decide) (by decide) run
 let first:=setVarHOLFinite (ofString "s") (.val (.word start)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 3)=_ at firstRun
 rw [source_memory_cost_one_3] at firstRun
 obtain ⟨size,secondPost,secondOutput,secondRun,secondScope,_,_,secondCode,_,_⟩:=
  memory_cost_pure_declaration_returned first firstOutput (ofString "n") (ofString "sat_word") _ (memoryCostOneAt 4) value (firstCode.trans code) (by decide) (by decide) firstRun
 let second:=setVarHOLFinite (ofString "n") (.val (.word size)) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 4)=_ at secondRun
 rw [source_memory_cost_one_4] at secondRun
 obtain ⟨endpoint,thirdPost,thirdOutput,thirdRun,thirdScope,_,_,thirdCode,_,_⟩:=
  memory_cost_pure_declaration_returned second secondOutput (ofString "endp") (ofString "add_sat") _ (memoryCostOneAt 5) value (secondCode.trans (firstCode.trans code)) (by decide) (by decide) secondRun
 let third:=setVarHOLFinite (ofString "endp") (.val (.word endpoint)) {thirdPost with locals:=second.locals}
 change evaluateHOLFiniteState third (memoryCostOneAt 5)=_ at thirdRun
 have endp : third.locals.lookup (ofString "endp")=some (.val (.word endpoint)) := by
  simp [third,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have cmp : @evalHOLExact 64 F _ third.toExact (fun a=>Classical.propDecidable (third.memaddrs a))
  (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615))=
  some (.val (.word (if endpoint=18446744073709551615#64 then 1 else 0))) := by
  simp [evalHOLExact,endp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_one_5] at thirdRun
 rcases memory_cost_guard_returned third thirdOutput _ _ 18446744073709551615 (memoryCostOneAt 6) value cmp thirdRun with returned|⟨_,tailRun⟩
 · rw [returned];exact memory_expansion_size_zero _
 · exact memory_cost_one_loaded_size third thirdOutput value (thirdCode.trans (secondCode.trans (firstCode.trans code))) tailRun

/-- Whole original cost1 has a uniform actual expansion ceiling independent
of gas/input/entry argument shape. Bad reads/calls cannot produce a return. -/
theorem memory_cost_one_returned_size_bound {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_extend_memory_cost1)=(some (.returned value),post)) :
 MemoryExpansionSizeBound (2^37) value := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryCostOneAt 0)=_ at run
 rw [source_memory_cost_one_0] at run
 obtain ⟨zeroWord,firstPost,firstOutput,firstRun,firstScope,_,_,installed,_,_⟩:=
  memory_cost_pure_declaration_returned s post (ofString "z") (ofString "u256_is_zero") _ (memoryCostOneAt 1) value code (by decide) (by decide) run
 let first:=setVarHOLFinite (ofString "z") (.val (.word zeroWord)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 1)=_ at firstRun
 have z : first.locals.lookup (ofString "z")=some (.val (.word zeroWord)) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have cmp : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.cmp .notEqual (.var .local (ofString "z")) (.const 0))=
  some (.val (.word (if zeroWord=0#64 then 0 else 1))) := by
  simp [evalHOLExact,z,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_one_1] at firstRun
 rcases memory_cost_guard_returned first firstOutput _ _ 0 (memoryCostOneAt 2) value cmp firstRun with returned|⟨_,tailRun⟩
 · rw [returned];exact memory_expansion_size_zero _
 · exact memory_cost_one_preparation_size first firstOutput value (installed.trans code) tailRun
#print axioms memory_cost_one_rounding_size
#print axioms memory_cost_one_loaded_size
#print axioms memory_cost_one_preparation_size
#print axioms memory_cost_one_returned_size_bound
end InitECandidate.Runtime
