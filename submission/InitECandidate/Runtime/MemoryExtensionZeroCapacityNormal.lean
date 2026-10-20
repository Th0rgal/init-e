import InitECandidate.Runtime.MemoryExtensionSource
import InitECandidate.Runtime.MemzeroNormalUpperFrame
import InitECandidate.Runtime.EncodeHeaderNormalPlan
import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Actual newly added EVM-memory zeroing followed by the original capacity
store. All memory at/above scratch is kept except the real ev+40 update. -/
theorem memory_extension_zero_capacity_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base capacity newCapacity scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atNewCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word newCapacity)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (capacityOrder : capacity.toNat≤newCapacity.toNat)
 (extent : base.toNat+newCapacity.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryExtensionGrowthAt 3)=(none,post)) :
 post.memory (frame+40)=.word newCapacity ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+40 → post.memory watched=s.memory watched) ∧
 post.globals=s.globals ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 classical
 rw [source_memory_extension_growth_3] at run
 obtain ⟨zeroPost,zeroRun,storeRun⟩:=encode_header_seq_normal s post _ _ run
 have loaded:=eval_fundingLoad s frame (24#64) base atFrame baseDomain baseAt
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.load .one (fundingAddress (24#64)))=some (.val (.word base)) at loaded
 have destination : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "cap")])=some (.val (.word (base+capacity))) := by
  rw [evalHOLExact,evalListHOLExact,loaded]
  simp [evalListHOLExact,evalHOLExact,atCapacity,wordOpHOL,wordOp,valueIsWord,valueWord]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .add [.load .one (fundingAddress 24),.var .local (ofString "cap")],.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]=
  some [.val (.word (base+capacity)),.val (.word (newCapacity-capacity))] := by
  change @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a))
   [.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "cap")],.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]=_
  rw [evalListHOLFinite,evalListHOLExact,destination]
  simp [evalListHOLExact,evalHOLExact,atCapacity,atNewCapacity,wordOpHOL,wordOp,valueIsWord,valueWord]
 have destinationNat : (base+capacity).toNat=base.toNat+capacity.toNat:=BitVec.toNat_add_of_lt (by omega)
 have sizeNat : (newCapacity-capacity).toNat=newCapacity.toNat-capacity.toNat:=BitVec.toNat_sub_of_le (BitVec.le_def.mpr capacityOrder)
 obtain ⟨memory,locals,globals,domain,endian,installed⟩:=memzero_normal_upper_frame s zeroPost _ (base+capacity) (newCapacity-capacity) scratch args (by rw [destinationNat,sizeNat];omega) scratchCap code zeroRun
 rw [source_memory_extension_growth_4] at storeRun
 have current : zeroPost.globals.lookup (ofString "ev")=some (.val (.word frame)) := by rw [globals];exact atFrame
 have valueEval : @evalHOLExact 64 F _ zeroPost.toExact (fun a=>Classical.propDecidable (zeroPost.memaddrs a))
  (.var .local (ofString "ncap"))=some (.val (.word newCapacity)) := by
  simpa [evalHOLExact,locals] using atNewCapacity
 have postEq:=store_normal_exact zeroPost post (fundingAddress 40) (.var .local (ofString "ncap")) (frame+40) newCapacity
  (eval_fundingAddress zeroPost frame 40 current) valueEval storeRun
 rw [postEq]
 refine ⟨?_,?_,globals,locals,domain,endian,installed⟩
 · change (if frame+40#64=frame+40#64 then HolWordLab.word newCapacity else _) = _
   rw [if_pos rfl]
 · intro watched above different
   change watched≠frame+40#64 at different
   change (if watched=frame+40#64 then HolWordLab.word newCapacity else zeroPost.memory watched)=_
   rw [if_neg different]
   exact memory watched above
#print axioms memory_extension_zero_capacity_normal
end InitECandidate.Runtime
