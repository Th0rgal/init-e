import InitECandidate.Runtime.MemoryCostTwoSizeTail
import InitECandidate.Runtime.MemoryCostOneBoundedDeclaration
import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual saved-length declaration, temporary length store, real second
cost1 call and restoration, followed by the original final pair. -/
theorem memory_cost_two_temporary_size {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame current firstFee firstExpansion : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+32)) (currentAt : s.memory (frame+32)=.word current)
 (atA : s.locals.lookup (ofString "a")=some (.rStruct [.val (.word firstFee),.val (.word firstExpansion)]))
 (firstBound : current.toNat+firstExpansion.toNat<2^64) (firstSize : firstExpansion.toNat<2^37)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryCostTwoAt 2)=(some (.returned value),post)) :
 MemoryExpansionSizeBound (2^38) value := by
 rw [source_memory_cost_two_2] at run
 obtain ⟨saved,firstOutput,savedEval,firstRun,firstScope⟩:=funding_declaration_returned_context run
 have loaded:=eval_fundingLoad s frame (32#64) current atFrame domain currentAt
 have equal : saved=.val (.word current):=Option.some.inj (savedEval.symm.trans loaded)
 subst saved
 let first:=setVarHOLFinite (ofString "saved") (.val (.word current)) s
 change evaluateHOLFiniteState first (memoryCostTwoAt 3)=_ at firstRun
 have savedAt : first.locals.lookup (ofString "saved")=some (.val (.word current)) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have aAt : first.locals.lookup (ofString "a")=some (.rStruct [.val (.word firstFee),.val (.word firstExpansion)]) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atA
 have increasedEval : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.op .add [.var .local (ofString "saved"),.rfield 1 (.var .local (ofString "a"))])=some (.val (.word (current+firstExpansion))) := by
  simp [evalHOLExact,evalListHOLExact,savedAt,aAt,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_memory_cost_two_3] at firstRun
 have grownRun:=funding_store_returned_context first firstOutput (fundingAddress 32) _ (frame+32) (current+firstExpansion) (memoryCostTwoAt 4) value
  (eval_fundingAddress first frame 32 atFrame) increasedEval firstRun
 let grown:=sourceWriteWord first (frame+32) (current+firstExpansion)
 change evaluateHOLFiniteState grown (memoryCostTwoAt 4)=_ at grownRun
 have grownCurrent : grown.memory (frame+32)=.word (current+firstExpansion) := by
  change (if frame+32#64=frame+32#64 then HolWordLab.word (current+firstExpansion) else _) = _
  rw [if_pos rfl]
 rw [source_memory_cost_two_4] at grownRun
 obtain ⟨secondFee,secondExpansion,bodyPost,secondOutput,secondRun,secondScope,secondBound,secondSize,bodyMemory,bodyGlobals,bodyCode,bodyDomain,_⟩:=
  memory_cost_one_bounded_declaration_returned grown firstOutput (ofString "b") _ (memoryCostTwoAt 5) frame (current+firstExpansion) value atFrame domain grownCurrent code grownRun
 let second:=setVarHOLFinite (ofString "b") (.rStruct [.val (.word secondFee),.val (.word secondExpansion)]) {bodyPost with locals:=grown.locals}
 change evaluateHOLFiniteState second (memoryCostTwoAt 5)=_ at secondRun
 have secondSaved : second.locals.lookup (ofString "saved")=some (.val (.word current)) := by
  simp (config:={decide:=true}) [second,grown,first,sourceWriteWord,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have secondFrame : second.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
  change bodyPost.globals.lookup _=_;rw [bodyGlobals];exact atFrame
 rw [source_memory_cost_two_5] at secondRun
 have restoredRun:=funding_store_returned_context second secondOutput (fundingAddress 32) (.var .local (ofString "saved")) (frame+32) current (memoryCostTwoAt 6) value
  (eval_fundingAddress second frame 32 secondFrame) (by simpa [evalHOLExact] using secondSaved) secondRun
 let restored:=sourceWriteWord second (frame+32) current
 change evaluateHOLFiniteState restored (memoryCostTwoAt 6)=_ at restoredRun
 have pairA : restored.locals.lookup (ofString "a")=some (.rStruct [.val (.word firstFee),.val (.word firstExpansion)]) := by
  simpa (config:={decide:=true}) [restored,second,grown,first,sourceWriteWord,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atA
 have pairB : restored.locals.lookup (ofString "b")=some (.rStruct [.val (.word secondFee),.val (.word secondExpansion)]) := by
  simp [restored,second,sourceWriteWord,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 exact memory_cost_two_tail_size restored secondOutput firstFee firstExpansion secondFee secondExpansion value pairA pairB firstSize secondSize restoredRun

#print axioms memory_cost_two_temporary_size
end InitECandidate.Runtime
