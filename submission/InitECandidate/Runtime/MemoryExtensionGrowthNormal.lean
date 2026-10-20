import InitECandidate.Runtime.MemoryExtensionCapacityClamp
import InitECandidate.Runtime.MemoryExtensionAllocationNormal
import InitECandidate.Runtime.MemoryExtensionZeroCapacityNormal
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.PanDecCallNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Complete actual extend_memory growth branch: real capacity calculation,
clamp, allocation, zeroing and header store. The allocator's own normal guards
supply the whole buffer extent; older words are retained outside ev+40. -/
theorem memory_extension_growth_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base capacity newLength pointer scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atLength : s.locals.lookup (ofString "nlen")=some (.val (.word newLength)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (lengthBound : newLength.toNat≤33806089496+2^38) (growing : capacity.toNat<newLength.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryExtensionGrowthAt 0)=(none,post)) :
 let grown:=memoryExtensionCapacity capacity newLength
 let next:=allocationEnd pointer (grown-capacity)
 post.memory (frame+40)=.word grown ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+40 → post.memory watched=s.memory watched) ∧
 post.globals=s.globals.update (ofString "frame_mem_ptr",.val (.word next)) ∧
 pointer.toNat≤next.toNat ∧base.toNat+grown.toNat≤next.toNat ∧next.toNat≤scratch.toNat ∧next.toNat%8=0 ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀key,key≠ofString "ncap" → post.locals.lookup key=s.locals.lookup key) := by
 have bounds:=memory_extension_capacity_bounds capacity newLength (by omega) lengthBound growing
 rw [source_memory_extension_growth_0] at run
 obtain ⟨value,output,evaluated,nextRun,postEq⟩:=evaluate_dec_normal_scope s post _ _ _ _ run
 have initial : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.panop .mul [.var .local (ofString "cap"),.const 2])=some (.val (.word (capacity*2#64))) := by
  simp [evalHOLExact,evalListHOLExact,atCapacity,panOpHOL,valueIsWord,valueWord]
 have equal : value=.val (.word (capacity*2#64)):=Option.some.inj (evaluated.symm.trans initial)
 subst value
 let first:=setVarHOLFinite (ofString "ncap") (.val (.word (capacity*2#64))) s
 change evaluateHOLFiniteState first (memoryExtensionGrowthAt 1)=_ at nextRun
 have declared : first.locals.lookup (ofString "ncap")=some (.val (.word (capacity*2#64))) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have newLengthAt : first.locals.lookup (ofString "nlen")=some (.val (.word newLength)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 obtain ⟨ready,allocationRun,ncap,clampMemory,clampGlobals,_,clampDomain,clampEndian,clampCode,clampLocals⟩:=
  memory_extension_capacity_clamp_normal first output capacity newLength declared newLengthAt nextRun
 have capAt : ready.locals.lookup (ofString "cap")=some (.val (.word capacity)) := by
  rw [clampLocals _ (by decide)]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCapacity
 obtain ⟨allocated,zeroRun,allocationGlobals,coverage,extent,within,aligned,allocationMemory,allocationLocals,allocationDomain,allocationEndian,allocationCode⟩:=
  memory_extension_allocation_normal ready output base capacity (memoryExtensionCapacity capacity newLength) pointer scratch capAt ncap
   (by rw [clampGlobals];exact atPointer) (by rw [clampGlobals];exact atScratch) oldExtent bounds.1 ordered scratchCap
   (clampCode.trans code) allocationRun
 have allocatedFrame : allocated.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
  rw [allocationGlobals,clampGlobals]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atFrame
 have memoryOld : allocated.memory=s.memory:=allocationMemory.trans clampMemory
 have domainOld : allocated.memaddrs=s.memaddrs:=allocationDomain.trans clampDomain
 have codeOld : allocated.code=originalRuntimeCode:=allocationCode.trans (clampCode.trans code)
 obtain ⟨capacityAt,memoryKept,globalsKept,localsKept,domainKept,endianKept,codeKept⟩:=
  memory_extension_zero_capacity_normal allocated output frame base capacity (memoryExtensionCapacity capacity newLength) scratch
   allocatedFrame (by rw [allocationLocals];exact capAt) (by rw [allocationLocals];exact ncap)
   (by rw [domainOld];exact baseDomain) (by rw [memoryOld];exact baseAt) bounds.1 (by omega) scratchCap codeOld zeroRun
 rw [postEq]
 refine ⟨capacityAt,?_,?_,by omega,extent,within,aligned,?_,?_,?_,?_⟩
 · intro watched above different
   exact (memoryKept watched above different).trans (congrArg (fun m=>m watched) memoryOld)
 · exact globalsKept.trans (allocationGlobals.trans (congrArg (fun g=>g.update (ofString "frame_mem_ptr",.val (.word (allocationEnd pointer (memoryExtensionCapacity capacity newLength-capacity))))) clampGlobals))
 · exact domainKept.trans domainOld
 · exact endianKept.trans (allocationEndian.trans clampEndian)
 · exact codeKept.trans (allocationCode.trans clampCode)
 · intro key different
   rw [saved_local_lookup_other _ _ _ _ different,localsKept,allocationLocals,clampLocals _ different]
   simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
#print axioms memory_extension_growth_normal
end InitECandidate.Runtime
