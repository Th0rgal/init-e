import InitECandidate.Runtime.MemoryExtensionGrowthZeroRuntimeBound
import InitECandidate.Runtime.FrameMemoryDiscardNormalContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual frame allocator plus growth zeroing: failures terminate within the
allocator bound; on its normal path the real space guards bound zeroing length.
No room or successful allocation is assumed. -/
theorem memory_extension_allocator_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base capacity newCapacity pointer scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atNewCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word newCapacity)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (ordered : pointer.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode) (budget : 3+memoryExtensionZeroCost≤s.clock) :
 RunBounded s (memoryExtensionGrowthAt 2) (3+memoryExtensionZeroCost) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]=some [.val (.word (newCapacity-capacity))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNewCapacity,atCapacity,wordOpHOL,wordOp,valueIsWord,valueWord]
 have allocator : RunBounded s (.call (some (none,none)) (ofString "frame_mem_alloc") [.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]) 3 :=
  RunBounded.ofProg (ProgBounded.call vmBound_frame_mem_alloc none _) code (by omega)
 rw [source_memory_extension_growth_2]
 apply RunBounded.seq allocator budget
 intro allocated ran installed remaining
 obtain ⟨globals,coverage,within,aligned,memory,locals,domain,endian,_⟩:=frame_memory_discard_normal_contract s allocated _ pointer (newCapacity-capacity) scratch args atPointer atScratch ordered cap code ran
 have small : (newCapacity-capacity).toNat≤33806089496 := by omega
 have sameFrame : allocated.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
  rw [globals]
  simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atFrame
 have sameCapacity : allocated.locals.lookup (ofString "cap")=some (.val (.word capacity)) := by rw [locals];exact atCapacity
 have sameNewCapacity : allocated.locals.lookup (ofString "ncap")=some (.val (.word newCapacity)) := by rw [locals];exact atNewCapacity
 have sameDomain : allocated.memaddrs (frame+24) := by rw [domain];exact baseDomain
 have sameBase : allocated.memory (frame+24)=.word base := by rw [memory];exact baseAt
 exact memory_extension_growth_zero_bounded allocated frame base capacity newCapacity sameFrame sameCapacity sameNewCapacity sameDomain sameBase small (installed.trans code) remaining
#print axioms memory_extension_allocator_suffix_bounded
end InitECandidate.Runtime
