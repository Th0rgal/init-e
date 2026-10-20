import InitECandidate.Runtime.MemoryExtensionGrowthRuntimeBound
import InitECandidate.Runtime.MemoryExtensionGrowthNormal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
def memoryExtensionBodyCost : Nat:=3+memoryExtensionZeroCost+memoryExtensionZeroCost
/-- Actual growth choice and common tail have a fixed all-outcome budget.
The large requested expansion may fail allocation; any normal growth path
itself proves the reached final zeroing size is below scratch. -/
theorem memory_extension_choice_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base length capacity expansion newLength pointer scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atLength : s.locals.lookup (ofString "len")=some (.val (.word length)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atExpansion : s.locals.lookup (ofString "expand_by")=some (.val (.word expansion)))
 (atNewLength : s.locals.lookup (ofString "nlen")=some (.val (.word newLength)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat) (lengthSum : newLength.toNat=length.toNat+expansion.toNat)
 (expansionBound : expansion.toNat<2^38)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤frame.toNat) (frameExtent : frame.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode) (budget : memoryExtensionBodyCost≤s.clock) :
 RunBounded s (memoryExtensionAt 4) memoryExtensionBodyCost := by
 have scratchCap : scratch.toNat≤33806089496:=by omega
 have capacityCap : capacity.toNat≤33806089496:=by omega
 have lengthBound : newLength.toNat≤33806089496+2^38:=by omega
 have growth:=memory_extension_growth_bounded s frame base capacity newLength pointer scratch atFrame atCapacity atNewLength baseDomain baseAt atPointer atScratch ordered scratchCap code (by unfold memoryExtensionBodyCost at budget;omega)
 have skipped : RunBounded s (.skip : ProgHOL 64) (3+memoryExtensionZeroCost) :=
  (RunBounded.ofProg (ProgBounded.straight .skip (by decide)) code (by omega)).weaken (by omega)
 have choice:=RunBounded.ite_cases growth skipped (condition:=.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))
 rw [source_memory_extension_4]
 apply RunBounded.seq choice budget
 intro next ran installed remaining
 by_cases growing : capacity.toNat<newLength.toNat
 · have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))=some (.val (.word 1)) := by
    simp [evalHOLExact,atCapacity,atNewLength,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,growing]
   rw [evaluateHOLFiniteState_ite,condition] at ran
   change evaluateHOLFiniteState s (memoryExtensionGrowthAt 0)=(none,next) at ran
   obtain ⟨capacityAt,protectedMemory,globals,mono,extent,within,aligned,domain,endian,_,locals⟩:=memory_extension_growth_normal s next frame base capacity newLength pointer scratch atFrame atCapacity atNewLength baseDomain baseAt atPointer atScratch oldExtent ordered scratchCap lengthBound growing code ran
   have bounds:=memory_extension_capacity_bounds capacity newLength capacityCap lengthBound growing
   have small : expansion.toNat≤33806089496:=by omega
   have frameAt : next.globals.lookup (ofString "ev")=some (.val (.word frame)) := by
    rw [globals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atFrame
   have lengthAt : next.locals.lookup (ofString "len")=some (.val (.word length)) := by rw [locals _ (by decide)];exact atLength
   have expansionAt : next.locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by rw [locals _ (by decide)];exact atExpansion
   have domainAt : next.memaddrs (frame+24) := by rw [domain];exact baseDomain
   have natural : (frame+24#64).toNat=frame.toNat+24:=BitVec.toNat_add_of_lt (by change frame.toNat+24<2^64;omega)
   have baseKept : next.memory (frame+24)=.word base := by
    rw [protectedMemory (frame+24) (by change scratch.toNat≤(frame+24#64).toNat;rw [natural];omega) (by simp)]
    exact baseAt
   exact memory_extension_final_suffix_bounded next frame base length expansion frameAt lengthAt expansionAt domainAt baseKept small (installed.trans code) remaining
 · have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))=some (.val (.word 0)) := by
    simp [evalHOLExact,atCapacity,atNewLength,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,growing]
   rw [evaluateHOLFiniteState_ite,condition] at ran
   change evaluateHOLFiniteState s .skip=(none,next) at ran
   rw [evaluateHOLFiniteState_skip] at ran
   have equal : next=s:=(Prod.mk.inj ran).2.symm
   subst next
   exact memory_extension_final_suffix_bounded s frame base length expansion atFrame atLength atExpansion baseDomain baseAt (by omega) code remaining
#print axioms memory_extension_choice_bounded
end InitECandidate.Runtime
