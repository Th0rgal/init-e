import InitECandidate.Runtime.MemoryExtensionAllocatorRuntimeBound
import InitECandidate.Runtime.HtabSetBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Whole real growth branch, with its actual capacity declaration/clamp and
all allocator/error outcomes. The allocator bounds any reached zeroing call. -/
theorem memory_extension_growth_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base capacity newLength pointer scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atLength : s.locals.lookup (ofString "nlen")=some (.val (.word newLength)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (ordered : pointer.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode) (budget : 3+memoryExtensionZeroCost≤s.clock) :
 RunBounded s (memoryExtensionGrowthAt 0) (3+memoryExtensionZeroCost) := by
 have initial : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.panop .mul [.var .local (ofString "cap"),.const 2])=some (.val (.word (capacity*2#64))) := by
  simp [evalHOLExact,evalListHOLExact,atCapacity,panOpHOL,valueIsWord,valueWord]
 rw [source_memory_extension_growth_0]
 apply RunBounded.decWord s _ _ (capacity*2#64) initial
 let first:=setVarHOLFinite (ofString "ncap") (.val (.word (capacity*2#64))) s
 change RunBounded first (memoryExtensionGrowthAt 1) _
 have firstCapacity : first.locals.lookup (ofString "cap")=some (.val (.word capacity)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCapacity
 have firstLength : first.locals.lookup (ofString "nlen")=some (.val (.word newLength)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 have firstNewCapacity : first.locals.lookup (ofString "ncap")=some (.val (.word (capacity*2#64))) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_memory_extension_growth_1]
 have clamp : RunBounded first (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen"))) (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"),.const 1024])) .skip) 0 :=
  RunBounded.ofProg (ProgBounded.straight _ (by decide_cbv)) code (by omega)
 have result:=RunBounded.seq clamp (b:=3+memoryExtensionZeroCost) (by simpa [first,setVarHOLFinite] using budget) (by
  intro ready ran installed remaining
  rcases ite_normal_cases first ready _ _ _ ran with assigned|skipped
  · have evaluated : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
     (.op .add [.var .local (ofString "nlen"),.const 1024])=some (.val (.word (newLength+1024#64))) := by
     simp [evalHOLExact,evalListHOLExact,firstLength,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [evaluateHOLFiniteState_assign,evaluated] at assigned
    dsimp only at assigned
    split at assigned
    · have equal : ready=setKvarHOLFinite .local (ofString "ncap") (.val (.word (newLength+1024#64))) first:=(Prod.mk.inj assigned).2.symm
      subst ready
      have capacityAt : (setKvarHOLFinite .local (ofString "ncap") (.val (.word (newLength+1024#64))) first).locals.lookup (ofString "cap")=some (.val (.word capacity)) := by
       simpa (config:={decide:=true}) [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using firstCapacity
      have newCapacityAt : (setKvarHOLFinite .local (ofString "ncap") (.val (.word (newLength+1024#64))) first).locals.lookup (ofString "ncap")=some (.val (.word (newLength+1024#64))) := by
       simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      exact memory_extension_allocator_suffix_bounded _ frame base capacity (newLength+1024#64) pointer scratch atFrame capacityAt newCapacityAt baseDomain baseAt atPointer atScratch ordered cap code remaining
    · cases assigned
  · rw [evaluateHOLFiniteState_skip] at skipped
    have equal : ready=first:=(Prod.mk.inj skipped).2.symm
    subst ready
    exact memory_extension_allocator_suffix_bounded first frame base capacity (capacity*2#64) pointer scratch atFrame firstCapacity firstNewCapacity baseDomain baseAt atPointer atScratch ordered cap code remaining)
 simpa only [Nat.zero_add] using result
#print axioms memory_extension_growth_bounded
end InitECandidate.Runtime
