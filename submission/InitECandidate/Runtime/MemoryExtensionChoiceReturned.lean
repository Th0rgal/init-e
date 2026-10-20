import InitECandidate.Runtime.MemoryExtensionGrowthNormal
import InitECandidate.Runtime.MemoryExtensionFinalSuffix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Original extend_memory growth/no-growth choice through the actual return,
retaining the physical EVM buffer and protecting every older word except its
real length/capacity fields. -/
theorem memory_extension_choice_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base length capacity expansion newLength pointer scratch : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atLength : s.locals.lookup (ofString "len")=some (.val (.word length)))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (atExpansion : s.locals.lookup (ofString "expand_by")=some (.val (.word expansion)))
 (atNewLength : s.locals.lookup (ofString "nlen")=some (.val (.word newLength)))
 (baseDomain : s.memaddrs (frame+24)) (baseAt : s.memory (frame+24)=.word base)
 (capacityAt : s.memory (frame+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat) (lengthSum : newLength.toNat=length.toNat+expansion.toNat)
 (expansionBound : expansion.toNat<2^38) (oldExtent : base.toNat+capacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat) (belowFrame : scratch.toNat≤frame.toNat)
 (frameExtent : frame.toNat+280≤33806089496) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (memoryExtensionAt 4)=(some (.returned value),post)) :
 value=.val (.word (0#64)) ∧
 ∃newCapacity nextPointer : BitVec 64,
 post.memory (frame+24)=.word base ∧post.memory (frame+32)=.word newLength ∧post.memory (frame+40)=.word newCapacity ∧
 newLength.toNat≤newCapacity.toNat ∧base.toNat+newCapacity.toNat≤nextPointer.toNat ∧
 pointer.toNat≤nextPointer.toNat ∧nextPointer.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "ev")=some (.val (.word frame)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word nextPointer)) ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+32 → watched≠frame+40 → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (memoryExtensionAt 4)
 rw [run] at metadata
 have above24 : scratch.toNat≤(frame+24#64).toNat := by
  rw [BitVec.toNat_add_of_lt (by change frame.toNat+24<2^64;omega)];change scratch.toNat≤frame.toNat+24;omega
 have above40 : scratch.toNat≤(frame+40#64).toNat := by
  rw [BitVec.toNat_add_of_lt (by change frame.toNat+40<2^64;omega)];change scratch.toNat≤frame.toNat+40;omega
 have different2432 : frame+24#64≠frame+32#64 := by intro equal;have h : (24#64)=(32#64):=add_left_cancel equal;contradiction
 have different2440 : frame+24#64≠frame+40#64 := by intro equal;have h : (24#64)=(40#64):=add_left_cancel equal;contradiction
 have different4032 : frame+40#64≠frame+32#64 := by intro equal;have h : (40#64)=(32#64):=add_left_cancel equal;contradiction
 rw [source_memory_extension_4] at run
 obtain ⟨middle,growthRun,suffixRun⟩:=seq_returned_of_nonreturning_first
  (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) s v) run
 have ready : ∃grown next : BitVec 64,
  middle.memory (frame+24)=.word base ∧middle.memory (frame+40)=.word grown ∧
  newLength.toNat≤grown.toNat ∧base.toNat+grown.toNat≤next.toNat ∧pointer.toNat≤next.toNat ∧next.toNat≤scratch.toNat ∧
  middle.globals.lookup (ofString "ev")=some (.val (.word frame)) ∧
  middle.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
  middle.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word next)) ∧
  middle.memaddrs=s.memaddrs ∧middle.code=s.code ∧
  (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+40 → middle.memory watched=s.memory watched) ∧
  (∀key,key≠ofString "ncap" → middle.locals.lookup key=s.locals.lookup key) := by
  by_cases growing : capacity.toNat<newLength.toNat
  · have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))=some (.val (.word 1)) := by
     simp [evalHOLExact,atCapacity,atNewLength,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,growing]
    rw [evaluateHOLFiniteState_ite,cmp] at growthRun
    change evaluateHOLFiniteState s (memoryExtensionGrowthAt 0)=(none,middle) at growthRun
    obtain ⟨capAt,memory,globals,monotone,extent,within,aligned,domain,endian,installed,locals⟩:=
     memory_extension_growth_normal s middle frame base capacity newLength pointer scratch atFrame atCapacity atNewLength baseDomain baseAt atPointer atScratch oldExtent ordered (by omega) (by omega) growing code growthRun
    have bounds:=memory_extension_capacity_bounds capacity newLength (by omega) (by omega) growing
    refine ⟨_,_,(memory _ above24 different2440).trans baseAt,capAt,bounds.2.1,extent,monotone,within,?_,?_,?_,domain,installed,memory,locals⟩
    · rw [globals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atFrame
    · rw [globals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atScratch
    · rw [globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
     (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))=some (.val (.word 0)) := by
     simp [evalHOLExact,atCapacity,atNewLength,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,growing]
    rw [evaluateHOLFiniteState_ite,cmp] at growthRun
    change evaluateHOLFiniteState s .skip=(none,middle) at growthRun
    rw [evaluateHOLFiniteState_skip] at growthRun
    have equal : middle=s:=(Prod.mk.inj growthRun).2.symm
    subst middle
    exact ⟨capacity,pointer,baseAt,capacityAt,by omega,oldExtent,by omega,ordered,atFrame,atScratch,atPointer,rfl,rfl,by intros;rfl,by intros;rfl⟩
 obtain ⟨grown,next,baseReady,capacityReady,newLengthBound,extent,monotone,within,frameReady,scratchReady,pointerReady,domainReady,codeReady,memoryReady,localsReady⟩:=ready
 have lenReady : middle.locals.lookup (ofString "len")=some (.val (.word length)) := by rw [localsReady _ (by decide)];exact atLength
 have expReady : middle.locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by rw [localsReady _ (by decide)];exact atExpansion
 have nlenReady : middle.locals.lookup (ofString "nlen")=some (.val (.word newLength)) := by rw [localsReady _ (by decide)];exact atNewLength
 obtain ⟨returned,lengthAt,memory,globals,_,_,_⟩:=memory_extension_final_suffix_returned middle post frame base length expansion newLength scratch value frameReady lenReady expReady nlenReady (by rw [domainReady];exact baseDomain) baseReady lengthSum (by omega) (by omega) (codeReady.trans code) suffixRun
 refine ⟨returned,grown,next,(memory _ above24 different2432).trans baseReady,lengthAt,(memory _ above40 different4032).trans capacityReady,newLengthBound,extent,monotone,within,?_,?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [globals];exact frameReady
 · rw [globals];exact scratchReady
 · rw [globals];exact pointerReady
 · intro watched above different32 different40
   exact (memory watched above different32).trans (memoryReady watched above different40)
#print axioms memory_extension_choice_returned
end InitECandidate.Runtime
