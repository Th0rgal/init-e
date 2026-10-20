import InitECandidate.Runtime.EvmOperandStackGrowingBody
import InitECandidate.Runtime.EvmOperandStackNoGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Unified original stack_push protection for older frame words. The stack
buffer is concretely below its owner, and the real capacity invariant selects
the checked no-growth or growth path; no callback is part of this contract. -/
theorem stack_push_protected_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base index capacity scratch frontier a b c d watched : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (frame+offset))
 (baseAt : s.memory (frame+8)=.word base) (indexAt : s.memory (frame+16)=.word index)
 (capacityAt : s.memory (frame+232)=.word capacity)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤frame.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤frame.toNat)
 (frameExtent : frame.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (above : frame.toNat≤watched.toNat) (differentBase : watched≠frame+8)
 (differentCounter : watched≠frame+16) (differentCapacity : watched≠frame+232)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushAt 0)=(some (.returned value),post)) :
 value=.val (.word 0) ∧post.memory watched=s.memory watched ∧post.memaddrs=s.memaddrs ∧
 post.be=s.be ∧post.code=s.code ∧
 ∃nextScratch : BitVec 64,
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word nextScratch)) ∧
 nextScratch.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)) ∧
 post.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
 by_cases inside : index.toNat<capacity.toNat
 · have destinations:=stack_push_fresh_destinations_domain s base index capacity frame (by omega) capacityBound bufferExtent (by omega) fullDomain
   obtain ⟨returned,memory,globals,clock,domain,endian,installed⟩:=
    stack_push_no_growth_returned s post frame base index capacity a b c d value atCurrent atValue headerDomain baseAt indexAt capacityAt inside capacityBound destinations run
   refine ⟨returned,?_,domain,endian,installed,scratch,?_,by omega,?_,?_⟩
   · rw [memory]
     exact stack_push_write_suffix_frame s frame base index a b c d watched differentCounter
      (stack_push_fresh_destinations_separate base index capacity frame watched (by omega) capacityBound bufferExtent (by omega) above)
   · rw [globals];exact atScratch
   · rw [globals];exact atFrontier
   · rw [globals];exact atCurrent
 · have equal : index=capacity:=BitVec.eq_of_toNat_eq (by omega)
   subst capacity
   obtain ⟨returned,memory,counter,baseAtPost,capacityAtPost,globals,lower,extent,newInside,newBound,domain,endian,installed⟩:=
    stack_push_growing_body_returned s post frame base index scratch frontier a b c d watched value atCurrent atValue headerDomain baseAt indexAt capacityAt positive atScratch atFrontier ordered scratchBeforeFrame frameExtent (by omega)
     fullDomain (by omega) differentBase differentCounter differentCapacity code run
   refine ⟨returned,memory,domain,endian,installed,scratchAllocationEnd scratch (stackPushGrownCapacity index*32#64),?_,by omega,?_,?_⟩
   · rw [globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
   · rw [globals]
     simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atFrontier
   · rw [globals]
     simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atCurrent
#print axioms stack_push_protected_returned
end InitECandidate.Runtime
