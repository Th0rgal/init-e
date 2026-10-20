import InitECandidate.Runtime.EvmOperandStackGrowthCopyTail
import InitECandidate.Runtime.ScratchDeclarationNormalContract
import InitECandidate.Runtime.PanDecCallNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual growth allocation/copy path exports the real fresh stack extent
and retains every watched older word except the two real header updates.
Both allocation guards come from the normally completed source call. -/
theorem stack_push_growth_allocation_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame oldBase index capacity scratch frontier watched : BitVec 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atIndex : s.locals.lookup (ofString "sp")=some (.val (.word index)))
 (atCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word capacity)))
 (baseDomain : s.memaddrs (frame+8)) (baseAt : s.memory (frame+8)=.word oldBase)
 (indexBound : index.toNat≤capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchCap : scratch.toNat≤33806089496)
 (above : scratch.toNat≤watched.toNat) (differentBase : watched≠frame+8)
 (differentCapacity : watched≠frame+232) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushGrowthAt 3)=(none,post)) :
 let fresh:=scratchAllocationEnd scratch (capacity*32#64)
 post.memory (frame+8)=.word fresh ∧post.memory (frame+232)=.word capacity ∧
 post.memory watched=s.memory watched ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word fresh)) ∧
 frontier.toNat≤fresh.toNat ∧fresh.toNat+capacity.toNat*32≤scratch.toNat ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀key,key≠ofString "ns" → post.locals.lookup key=s.locals.lookup key) := by
 have sizeNat : (capacity*32#64).toNat=capacity.toNat*32 := by
  rw [BitVec.toNat_mul_of_lt (by change capacity.toNat*32<2^64;omega)];rfl
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.panop .mul [.var .local (ofString "ncap"),.const 32]]=some [.val (.word (capacity*32#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atCapacity,panOpHOL,valueIsWord,valueWord]
 rw [source_stack_push_growth_3] at run
 obtain ⟨allocated,output,tailRun,postEq,memory,domain,endian,installed,globals,lower,extent⟩:=
  scratch_declaration_normal_contract s post (ofString "ns") _ (stackPushGrowthAt 4) scratch (capacity*32#64) frontier args atScratch atFrontier ordered code run
 let ready:=setVarHOLFinite (ofString "ns") (.val (.word (scratchAllocationEnd scratch (capacity*32#64)))) {allocated with locals:=s.locals}
 change evaluateHOLFiniteState ready (stackPushGrowthAt 4)=(none,output) at tailRun
 have current : ready.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,globals,HolFiniteMapExact.lookup_update,FUPDATE] using atCurrent
 have ns : ready.locals.lookup (ofString "ns")=some (.val (.word (scratchAllocationEnd scratch (capacity*32#64)))) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have sp : ready.locals.lookup (ofString "sp")=some (.val (.word index)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atIndex
 have ncap : ready.locals.lookup (ofString "ncap")=some (.val (.word capacity)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCapacity
 have copied:=stack_push_growth_copy_tail_normal ready output frame oldBase _ index capacity scratch watched current ns sp ncap
  (by change allocated.memaddrs _;rw [domain];exact baseDomain)
  (by change allocated.memory _=_;rw [memory];exact baseAt) indexBound capacityBound
  (by simpa only [sizeNat] using extent) scratchCap above differentBase differentCapacity
  (by change allocated.code=_;exact installed.trans code) tailRun
 obtain ⟨newBase,newCapacity,kept,locals,globalKept,domainKept,endianKept,codeKept⟩:=copied
 rw [postEq]
 refine ⟨newBase,newCapacity,?_,?_,lower,?_,?_,?_,?_,?_⟩
 · exact kept.trans (congrArg (fun m=>m watched) memory)
 · exact globalKept.trans globals
 · simpa only [sizeNat] using extent
 · exact domainKept.trans domain
 · exact endianKept.trans endian
 · exact codeKept.trans installed
 · intro key different
   rw [saved_local_lookup_other _ _ _ _ different,locals]
   simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
#print axioms stack_push_growth_allocation_normal
end InitECandidate.Runtime
