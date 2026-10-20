import InitECandidate.Runtime.EvmOperandStackCapacityClamp
import InitECandidate.Runtime.EvmOperandStackGrowthAllocation
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Actual capacity declaration, real clamp, scratch allocation, memcpy and
header updates. This is the original growth suffix, with successful guards
extracted rather than a supplied callee/frame execution. -/
theorem stack_push_growth_resized_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame oldBase index capacity scratch frontier watched : BitVec 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atIndex : s.locals.lookup (ofString "sp")=some (.val (.word index)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (baseDomain : s.memaddrs (frame+8)) (baseAt : s.memory (frame+8)=.word oldBase)
 (indexBound : index.toNat≤capacity.toNat) (positive : 1≤capacity.toNat) (small : capacity.toNat<1024)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchCap : scratch.toNat≤33806089496)
 (above : scratch.toNat≤watched.toNat) (differentBase : watched≠frame+8)
 (differentCapacity : watched≠frame+232) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushGrowthAt 1)=(none,post)) :
 let grown:=stackPushGrownCapacity capacity
 let fresh:=scratchAllocationEnd scratch (grown*32#64)
 post.memory (frame+8)=.word fresh ∧post.memory (frame+232)=.word grown ∧
 post.memory watched=s.memory watched ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word fresh)) ∧
 frontier.toNat≤fresh.toNat ∧fresh.toNat+grown.toNat*32≤scratch.toNat ∧
 index.toNat+1≤grown.toNat ∧grown.toNat≤1024 ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀key,key≠ofString "ncap" → key≠ofString "ns" → post.locals.lookup key=s.locals.lookup key) := by
 have grownBound:=stack_push_grown_capacity_bounds capacity positive small
 rw [source_stack_push_growth_1] at run
 obtain ⟨value,output,evaluated,nextRun,postEq⟩:=evaluate_dec_normal_scope s post _ _ _ _ run
 have valueEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.panop .mul [.var .local (ofString "cap"),.const 2])=some (.val (.word (capacity*2))) := by
  simp [evalHOLExact,evalListHOLExact,atCapacity,panOpHOL,valueIsWord,valueWord]
 have valueEq : value=.val (.word (capacity*2)):=Option.some.inj (evaluated.symm.trans valueEval)
 subst value
 let first:=setVarHOLFinite (ofString "ncap") (.val (.word (capacity*2))) s
 change evaluateHOLFiniteState first (stackPushGrowthAt 2)=(none,output) at nextRun
 have declared : first.locals.lookup (ofString "ncap")=some (.val (.word (capacity*2))) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨ready,tailRun,ncap,memory,globals,clock,domain,endian,installed,other⟩:=
  stack_push_capacity_clamp_normal first output capacity small declared nextRun
 have sp : ready.locals.lookup (ofString "sp")=some (.val (.word index)) := by
  rw [other _ (by decide)]
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atIndex
 have allocated:=stack_push_growth_allocation_normal ready output frame oldBase index (stackPushGrownCapacity capacity) scratch frontier watched
  (by rw [globals];exact atCurrent) sp ncap
  (by rw [domain];exact baseDomain) (by rw [memory];exact baseAt)
  (by omega) grownBound.2 (by rw [globals];exact atScratch) (by rw [globals];exact atFrontier)
  ordered scratchCap above differentBase differentCapacity (by rw [installed];exact code) tailRun
 obtain ⟨newBase,newCapacity,kept,globalKept,lower,extent,domainKept,endianKept,codeKept,localsKept⟩:=allocated
 rw [postEq]
 refine ⟨newBase,newCapacity,?_,?_,lower,extent,by omega,grownBound.2,?_,?_,?_,?_⟩
 · exact kept.trans (congrArg (fun m=>m watched) memory)
 · exact globalKept.trans (congrArg (fun g=>g.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd scratch (stackPushGrownCapacity capacity*32#64))))) globals)
 · exact domainKept.trans domain
 · exact endianKept.trans endian
 · exact codeKept.trans installed
 · intro key differentNcap differentNs
   rw [saved_local_lookup_other _ _ _ _ differentNcap,localsKept _ differentNs,other _ differentNcap]
   simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,differentNcap,Ne.symm differentNcap]
#print axioms stack_push_growth_resized_normal
end InitECandidate.Runtime
