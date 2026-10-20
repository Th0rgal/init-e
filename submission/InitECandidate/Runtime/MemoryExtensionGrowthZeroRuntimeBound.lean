import InitECandidate.Runtime.MemoryExtensionZeroRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual growth zeroing and capacity store, including every invalid access.
The real allocator will supply the request bound on its normal path. -/
theorem memory_extension_growth_zero_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base capacity newCapacity : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atNewCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word newCapacity)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (small : (newCapacity-capacity).toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (budget : memoryExtensionZeroCost≤s.clock) :
 RunBounded s (memoryExtensionGrowthAt 3) memoryExtensionZeroCost := by
 have loaded:=eval_fundingLoad s frame (24#64) base atFrame baseDomain baseAt
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.load .one (fundingAddress (24#64)))=some (.val (.word base)) at loaded
 have destination : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "cap")])=some (.val (.word (base+capacity))) := by
  rw [evalHOLExact,evalListHOLExact,loaded]
  simp [evalListHOLExact,evalHOLExact,atCapacity,wordOpHOL,wordOp,valueIsWord,valueWord]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .add [.load .one (fundingAddress 24),.var .local (ofString "cap")],.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]=some [.val (.word (base+capacity)),.val (.word (newCapacity-capacity))] := by
  change @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) [.op .add [.load .one (fundingAddress (24#64)),.var .local (ofString "cap")],.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]=_
  rw [evalListHOLFinite,evalListHOLExact,destination]
  simp [evalListHOLExact,evalHOLExact,atNewCapacity,atCapacity,wordOpHOL,wordOp,valueIsWord,valueWord]
 have cost : (newCapacity-capacity).toNat/32+(newCapacity-capacity).toNat/8+11≤memoryExtensionZeroCost := by
  unfold memoryExtensionZeroCost
  have a:=Nat.div_le_div_right (c:=32) small
  have b:=Nat.div_le_div_right (c:=8) small
  omega
 have zero : RunBounded s (.call (some (none,none)) (ofString "memzero") [.op .add [.load .one (fundingAddress 24),.var .local (ofString "cap")],.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]) memoryExtensionZeroCost :=
  RunBounded.weaken (evaluate_memzero_call_bounded s _ (base+capacity) (newCapacity-capacity) args code small (by omega)) cost
 rw [source_memory_extension_growth_3]
 have result:=RunBounded.seq zero (b:=0) (by omega) (by
  intro next ran installed remaining
  exact RunBounded.ofProg (ProgBounded.straight (memoryExtensionGrowthAt 4) (by decide_cbv)) (installed.trans code) (by omega))
 simpa only [Nat.add_zero] using result
#print axioms memory_extension_growth_zero_bounded
end InitECandidate.Runtime
