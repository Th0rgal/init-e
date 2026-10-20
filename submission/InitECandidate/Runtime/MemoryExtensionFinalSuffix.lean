import InitECandidate.Runtime.MemoryExtensionSource
import InitECandidate.Runtime.MemzeroNormalUpperFrame
import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Actual final extend_memory zeroing and length store through its original
return. Protected old memory is retained outside ev+32. -/
theorem memory_extension_final_suffix_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base length expansion newLength scratch : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atLength : s.locals.lookup (ofString "len")=some (.val (.word length)))
 (atExpansion : s.locals.lookup (ofString "expand_by")=some (.val (.word expansion)))
 (atNewLength : s.locals.lookup (ofString "nlen")=some (.val (.word newLength)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (lengthSum : newLength.toNat=length.toNat+expansion.toNat)
 (extent : base.toNat+newLength.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryExtensionAt 5)=(some (.returned value),post)) :
 value=.val (.word (0#64)) ∧post.memory (frame+32)=.word newLength ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+32 → post.memory watched=s.memory watched) ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 classical
 have metadata:=evaluateHOLFiniteState_metadata s (memoryExtensionAt 5)
 rw [run] at metadata
 rw [source_memory_extension_5] at run
 obtain ⟨zeroPost,zeroRun,nextRun⟩:=seq_returned_of_nonreturning_first
  (fun v=>discard_call_not_returned s (ofString "memzero") _ v) run
 have loaded:=eval_fundingLoad s frame (24#64) base atFrame baseDomain baseAt
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.load .one (fundingAddress (24#64)))=some (.val (.word base)) at loaded
 have destination : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "len")])=some (.val (.word (base+length))) := by
  rw [evalHOLExact,evalListHOLExact,loaded]
  simp [evalListHOLExact,evalHOLExact,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .add [.load .one (fundingAddress 24),.var .local (ofString "len")],.var .local (ofString "expand_by")]=
  some [.val (.word (base+length)),.val (.word expansion)] := by
  change @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a))
   [.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "len")],.var .local (ofString "expand_by")]=_
  rw [evalListHOLFinite,evalListHOLExact,destination]
  simp [evalListHOLExact,evalHOLExact,atExpansion]
 have destinationNat : (base+length).toNat=base.toNat+length.toNat:=BitVec.toNat_add_of_lt (by omega)
 obtain ⟨memory,locals,globals,domain,endian,installed⟩:=memzero_normal_upper_frame s zeroPost _ (base+length) expansion scratch args (by rw [destinationNat];omega) scratchCap code zeroRun
 have current : zeroPost.globals.lookup (ofString "ev")=some (.val (.word frame)) := by rw [globals];exact atFrame
 have newLengthEval : @evalHOLExact 64 F _ zeroPost.toExact (fun a=>Classical.propDecidable (zeroPost.memaddrs a))
  (.var .local (ofString "nlen"))=some (.val (.word newLength)) := by
  simpa [evalHOLExact,locals] using atNewLength
 rw [source_memory_extension_6] at nextRun
 have finalRun:=funding_store_returned_context zeroPost post (fundingAddress 32) (.var .local (ofString "nlen")) (frame+32) newLength (memoryExtensionAt 7) value
  (eval_fundingAddress zeroPost frame 32 current) newLengthEval nextRun
 rw [source_memory_extension_7] at finalRun
 have returned : evaluateHOLFiniteState (sourceWriteWord zeroPost (frame+32) newLength) (.return (.const 0))=
  (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite (sourceWriteWord zeroPost (frame+32) newLength)) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
 obtain ⟨valueEq,postEq⟩:=Prod.mk.inj (finalRun.symm.trans returned)
 refine ⟨PanSemResultExact.returned.inj (Option.some.inj valueEq),?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [postEq]
   change (if frame+32#64=frame+32#64 then HolWordLab.word newLength else _) = _
   rw [if_pos rfl]
 · intro watched above different
   rw [postEq]
   change watched≠frame+32#64 at different
   change (if watched=frame+32#64 then HolWordLab.word newLength else zeroPost.memory watched)=_
   rw [if_neg different]
   exact memory watched above
 · rw [postEq];exact globals
#print axioms memory_extension_final_suffix_returned
end InitECandidate.Runtime
