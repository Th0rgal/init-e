import InitECandidate.Runtime.MemoryExtensionBodyReturnedFrame
import InitECandidate.Runtime.OriginalExtendMemoryCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Physical vector ownership after the actual installed discard extend_memory
call, derived from the same successful body run; caller locals are restored. -/
theorem memory_extension_discard_normal_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "extend_memory") arguments)=(none,post)) :
 post.locals=s.locals ∧
 ∃newCapacity nextPointer : BitVec 64,
 post.memory (frame+24)=.word base ∧post.memory (frame+32)=.word (length+expansion) ∧post.memory (frame+40)=.word newCapacity ∧
 (length+expansion).toNat≤newCapacity.toNat ∧base.toNat+newCapacity.toNat≤nextPointer.toNat ∧
 pointer.toNat≤nextPointer.toNat ∧nextPointer.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "ev")=some (.val (.word frame)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word nextPointer)) ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → watched≠frame+32 → watched≠frame+40 → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have installed : s.code.lookup (ofString "extend_memory")=some ([(ofString "expand_by",.one)],sourceFunctionBody Guest.guestFn_extend_memory,.one) := by
  rw [code];exact originalRuntimeCode_extendMemory_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "expand_by",.val (.word expansion))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "extend_memory") (ofString "expand_by") (sourceFunctionBody Guest.guestFn_extend_memory) expansion installed
 obtain ⟨value,bodyPost,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "extend_memory") arguments _ _ callee .one args lookup run
 obtain ⟨other,otherPost,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "extend_memory") arguments _ _ callee .one args lookup run
 have same : otherPost=bodyPost:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherPost
 have atExpansion : (callEntryStateHOLFinite s callee).locals.lookup (ofString "expand_by")=some (.val (.word expansion)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨_,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,lengthBound,extent,mono,within,evKept,scratchKept,pointerKept,frameKept,_,_,_⟩:=memory_extension_body_returned_frame (callEntryStateHOLFinite s callee) bodyPost frame base length capacity expansion pointer scratch value atFrame atExpansion headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder expansionBound oldExtent ordered belowFrame frameExtent code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "extend_memory") arguments)
 rw [run] at metadata
 refine ⟨locals,newCapacity,nextPointer,?_,?_,?_,lengthBound,extent,mono,within,?_,?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [memory];exact baseKept
 · rw [memory];exact lengthKept
 · rw [memory];exact capacityKept
 · rw [globals];exact evKept
 · rw [globals];exact scratchKept
 · rw [globals];exact pointerKept
 · intro watched above notLength notCapacity
   rw [memory];exact frameKept watched above notLength notCapacity
#print axioms memory_extension_discard_normal_frame
end InitECandidate.Runtime
