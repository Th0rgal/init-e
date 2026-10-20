import InitECandidate.Runtime.MemoryCostOneSource
import InitECandidate.Runtime.MemoryCostGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem memory_cost_one_final_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (current before after ca cb : BitVec 64) (value : ValueHOL 64)
 (atBefore : s.locals.lookup (ofString "before")=some (.val (.word before)))
 (atAfter : s.locals.lookup (ofString "after")=some (.val (.word after)))
 (atCa : s.locals.lookup (ofString "ca")=some (.val (.word ca)))
 (atCb : s.locals.lookup (ofString "cb")=some (.val (.word cb)))
 (beforeAbove : current.toNat≤before.toNat) (afterAbove : before.toNat<after.toNat)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 12)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615))=
  some (.val (.word (if ca=18446744073709551615#64 then 1 else 0))) := by
  simp [evalHOLExact,atCa,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_memory_cost_one_12] at run
 rcases memory_cost_guard_returned s post _ _ 18446744073709551615 (memoryCostOneAt 13) value cmp run with returned|⟨_,tailRun⟩
 · rw [returned];exact memory_expansion_zero current _
 · rw [source_memory_cost_one_13,evaluateHOLFiniteState_return] at tailRun
   have returned : value=.rStruct [.val (.word (ca-cb)),.val (.word (after-before))] := by
    simpa [evalHOLExact,evalListHOLExact,atCa,atCb,atBefore,atAfter,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL] using (Prod.mk.inj tailRun).1.symm
   refine ⟨ca-cb,after-before,returned,?_⟩
   rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
   have small:=after.isLt
   omega

/-- Actual final memory cost calls are read-only, so the guarded expansion
subtraction still uses exactly the real caller before/after words. -/
theorem memory_cost_one_calls_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (current before after : BitVec 64) (value : ValueHOL 64)
 (atBefore : s.locals.lookup (ofString "before")=some (.val (.word before)))
 (atAfter : s.locals.lookup (ofString "after")=some (.val (.word after)))
 (beforeAbove : current.toNat≤before.toNat) (afterAbove : before.toNat<after.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 10)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 rw [source_memory_cost_one_10] at run
 obtain ⟨ca,firstPost,firstOutput,firstRun,firstScope,_,_,firstCode,_,_⟩:=
  memory_cost_pure_declaration_returned s post (ofString "ca") (ofString "memory_gas_cost") _ (memoryCostOneAt 11) value code (by decide) (by decide) run
 let first:=setVarHOLFinite (ofString "ca") (.val (.word ca)) {firstPost with locals:=s.locals}
 change evaluateHOLFiniteState first (memoryCostOneAt 11)=_ at firstRun
 rw [source_memory_cost_one_11] at firstRun
 obtain ⟨cb,secondPost,secondOutput,secondRun,secondScope,_,_,secondCode,_,_⟩:=
  memory_cost_pure_declaration_returned first firstOutput (ofString "cb") (ofString "memory_gas_cost") _ (memoryCostOneAt 12) value (firstCode.trans code) (by decide) (by decide) firstRun
 let second:=setVarHOLFinite (ofString "cb") (.val (.word cb)) {secondPost with locals:=first.locals}
 change evaluateHOLFiniteState second (memoryCostOneAt 12)=_ at secondRun
 apply memory_cost_one_final_expansion second secondOutput current before after ca cb value _ _ _ _ beforeAbove afterAbove secondRun
 · simpa (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atBefore
 · simpa (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atAfter
 · simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Actual after/before guard includes every early-return outcome. -/
theorem memory_cost_one_guarded_expansion {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (current before after : BitVec 64) (value : ValueHOL 64)
 (atBefore : s.locals.lookup (ofString "before")=some (.val (.word before)))
 (atAfter : s.locals.lookup (ofString "after")=some (.val (.word after)))
 (beforeAbove : current.toNat≤before.toNat) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostOneAt 9)=(some (.returned value),post)) :
 MemoryExpansionResult current value := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))=
  some (.val (.word (if before.toNat<after.toNat then 0 else 1))) := by
  by_cases higher : before.toNat<after.toNat
  · simp [evalHOLExact,atBefore,atAfter,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,higher,Nat.not_le.mpr higher]
  · have lower : after.toNat≤before.toNat:=by omega
    simp [evalHOLExact,atBefore,atAfter,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,higher,lower]
 rw [source_memory_cost_one_9] at run
 rcases memory_cost_guard_returned s post _ _ 0 (memoryCostOneAt 10) value cmp run with returned|⟨zero,tailRun⟩
 · rw [returned];exact memory_expansion_zero current _
 · have higher : before.toNat<after.toNat := by
    by_contra notHigher
    simp [notHigher] at zero
   exact memory_cost_one_calls_expansion s post current before after value atBefore atAfter beforeAbove higher code tailRun

#print axioms memory_cost_one_guarded_expansion

#print axioms memory_cost_one_final_expansion
#print axioms memory_cost_one_calls_expansion
end InitECandidate.Runtime
