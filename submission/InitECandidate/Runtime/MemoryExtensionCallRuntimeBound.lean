import InitECandidate.Runtime.MemoryExtensionBodyRuntimeBound
import InitECandidate.Runtime.OriginalExtendMemoryCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual original installed extension discard-call bound includes every
callee outcome and the source call tick. No successful call is assumed. -/
theorem memory_extension_discard_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (frame base length capacity expansion pointer scratch : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word expansion)])
 (headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (frame+offset))
 (baseAt : s.memory (frame+24)=.word base) (lengthAt : s.memory (frame+32)=.word length)
 (capacityAt : s.memory (frame+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat) (expansionBound : expansion.toNat<2^38)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤frame.toNat) (frameExtent : frame.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode) (budget : memoryExtensionBodyCost+1≤s.clock) :
 RunBounded s (.call (some (none,none)) (ofString "extend_memory") arguments) (memoryExtensionBodyCost+1) := by
 have installed : s.code.lookup (ofString "extend_memory")=some ([(ofString "expand_by",.one)],sourceFunctionBody Guest.guestFn_extend_memory,.one) := by
  rw [code];exact originalRuntimeCode_extendMemory_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "expand_by",.val (.word expansion))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "extend_memory") (ofString "expand_by") (sourceFunctionBody Guest.guestFn_extend_memory) expansion installed
 apply RunBounded.call args budget
 intro body locals returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 have atExpansion : (callEntryStateHOLFinite s callee).locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 exact memory_extension_body_bounded (callEntryStateHOLFinite s callee) frame base length capacity expansion pointer scratch atFrame atExpansion headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder expansionBound oldExtent ordered belowFrame frameExtent code (by change memoryExtensionBodyCost≤s.clock-1;omega)
#print axioms memory_extension_discard_call_bounded
end InitECandidate.Runtime
