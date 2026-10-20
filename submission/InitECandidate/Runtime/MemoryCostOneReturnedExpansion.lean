import InitECandidate.Runtime.MemoryCostOneRoundingExpansion
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Real sat_word/add_sat prefix, including the saturated endpoint early exit.
All original helper executions are exposed from the same returned run. -/
theorem memory_cost_one_preparation_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 2)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 rw [source_memory_cost_one_2] at run
 obtain ⟨start,firstPost,firstOutput,firstRun,firstScope,firstMemory,firstGlobals,firstCode,firstDomain,_⟩:=
  memory_cost_pure_declaration_returned s post (ofString "s") (ofString "sat_word") _ (memoryCostOneAt 3) value code (by decide) (by decide) run
 let first:=setVarHOLFinite (ofString "s") (.val (.word start)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 3)=_ at firstRun
 rw [source_memory_cost_one_3] at firstRun
 obtain ⟨size,secondPost,secondOutput,secondRun,secondScope,secondMemory,secondGlobals,secondCode,secondDomain,_⟩:=
  memory_cost_pure_declaration_returned first firstOutput (ofString "n") (ofString "sat_word") _ (memoryCostOneAt 4) value (firstCode.trans code) (by decide) (by decide) firstRun
 let second:=setVarHOLFinite (ofString "n") (.val (.word size)) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 4)=_ at secondRun
 rw [source_memory_cost_one_4] at secondRun
 obtain ⟨endpoint,thirdPost,thirdOutput,thirdRun,thirdScope,thirdMemory,thirdGlobals,thirdCode,thirdDomain,_⟩:=
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
 · rw [returned];exact memory_expansion_zero current _
 · apply memory_cost_one_loaded_expansion third thirdOutput frame current value _ _ _ _ tailRun
   · change thirdPost.globals.lookup _=_
     have same : thirdPost.globals=s.globals := thirdGlobals.trans (secondGlobals.trans firstGlobals)
     rw [same];exact atFrame
   · change thirdPost.memaddrs _
     have same : thirdPost.memaddrs=s.memaddrs := thirdDomain.trans (secondDomain.trans firstDomain)
     rw [same];exact domain
   · change thirdPost.memory _=_
     have same : thirdPost.memory=s.memory := thirdMemory.trans (secondMemory.trans firstMemory)
     rw [same];exact currentAt
   · exact thirdCode.trans (secondCode.trans (firstCode.trans code))

/-- Whole actual original extend_memory_cost1 returns a typed pair whose real
expansion cannot wrap the current length. No gas, size, alignment, successful
callee/allocator execution, or returned-value callback is assumed. -/
theorem memory_cost_one_returned_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_extend_memory_cost1)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (memoryCostOneAt 0)=_ at run
 rw [source_memory_cost_one_0] at run
 obtain ⟨zeroWord,firstPost,firstOutput,firstRun,firstScope,memory,globals,installed,mapped,_⟩:=
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
 · rw [returned];exact memory_expansion_zero current _
 · apply memory_cost_one_preparation_expansion first firstOutput frame current value _ _ _ (installed.trans code) tailRun
   · change firstPost.globals.lookup _=_;rw [globals];exact atFrame
   · change firstPost.memaddrs _;rw [mapped];exact domain
   · change firstPost.memory _=_;rw [memory];exact currentAt
#print axioms memory_cost_one_preparation_expansion
#print axioms memory_cost_one_returned_expansion
end InitECandidate.Runtime
