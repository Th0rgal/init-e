import InitECandidate.Runtime.FrameMemoryDiscardNormalContract
import InitECandidate.Runtime.MemoryExtensionCapacityGeometry
import InitECandidate.Runtime.EncodeHeaderNormalPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual original extension allocation prefix exposes the same normal
continuation and derives the whole enlarged buffer extent from both real
allocator guards. No space or callee-execution assumption is supplied. -/
theorem memory_extension_allocation_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (base capacity newCapacity pointer scratch : BitVec 64)
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atNewCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word newCapacity)))
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (capacityOrder : capacity.toNat≤newCapacity.toNat)
 (ordered : pointer.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryExtensionGrowthAt 2)=(none,post)) :
 ∃allocated : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState allocated (memoryExtensionGrowthAt 3)=(none,post) ∧
 allocated.globals=s.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd pointer (newCapacity-capacity)))) ∧
 pointer.toNat+(newCapacity-capacity).toNat≤(allocationEnd pointer (newCapacity-capacity)).toNat ∧
 base.toNat+newCapacity.toNat≤(allocationEnd pointer (newCapacity-capacity)).toNat ∧
 (allocationEnd pointer (newCapacity-capacity)).toNat≤scratch.toNat ∧
 (allocationEnd pointer (newCapacity-capacity)).toNat%8=0 ∧
 allocated.memory=s.memory ∧allocated.locals=s.locals ∧allocated.memaddrs=s.memaddrs ∧allocated.be=s.be ∧allocated.code=s.code := by
 rw [source_memory_extension_growth_2] at run
 obtain ⟨allocated,allocationRun,tailRun⟩:=encode_header_seq_normal s post _ _ run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]=some [.val (.word (newCapacity-capacity))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atCapacity,atNewCapacity,wordOpHOL,wordOp,valueIsWord,valueWord]
 obtain ⟨globals,coverage,within,aligned,memory,locals,domain,endian,installed⟩:=
  frame_memory_discard_normal_contract s allocated _ pointer (newCapacity-capacity) scratch args atPointer atScratch ordered scratchCap code allocationRun
 have buffer:=memory_extension_buffer_extent base capacity newCapacity pointer (allocationEnd pointer (newCapacity-capacity)) scratch oldExtent capacityOrder coverage within
 exact ⟨allocated,tailRun,globals,coverage,buffer.1,within,aligned,memory,locals,domain,endian,installed⟩
#print axioms memory_extension_allocation_normal
end InitECandidate.Runtime
