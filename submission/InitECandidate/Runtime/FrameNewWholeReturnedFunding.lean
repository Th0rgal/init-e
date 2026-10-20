import InitECandidate.Runtime.FrameNewCopiesTailReturnedFunding
import InitECandidate.Runtime.FrameNewMarksReturnedContext
import InitECandidate.Runtime.FrameNewZeroPrefix
import InitECandidate.Runtime.FrameNewStackPrefix
import InitECandidate.Runtime.FrameNewMemoryPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Original frame_new, from its actual two marker calls through its actual
return: regular funding and both release marks, with concrete caller geometry. -/
theorem frame_new_whole_returned_funding {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame message codePointer codeLength accessAddresses accessSlots empty gas stateGas : BitVec 64) (value : ValueHOL 64)
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (atEmpty : s.globals.lookup (ofString "evm_empty")=some (.val (.word empty)))
 (ordered : frame.toNat≤scratch.toNat) (scratchCap : scratch.toNat≤33806089496)
 (beforeMessage : scratch.toNat≤message.toNat) (messageBound : message.toNat+176≤2^64)
 (messageDomain : ∀offset∈([112,120,152,160] : List (BitVec 64)),s.memaddrs (message+offset))
 (codeAt : s.memory (message+112)=.word codePointer) (lengthAt : s.memory (message+120)=.word codeLength)
 (addressesAt : s.memory (message+152)=.word accessAddresses) (slotsAt : s.memory (message+160)=.word accessSlots)
 (gasAt : s.memory (message+40)=.word gas) (stateGasAt : s.memory (message+48)=.word stateGas)
 (lengthBound : codeLength.toNat≤134217712) (sourceCode : s.code=originalRuntimeCode)
 (recordDomain : ∀offset : Nat,offset<280 → s.memaddrs (panByteAlignHOL (scratchAllocationEnd scratch 280+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s (frameNewAt 0)=(some (.returned value),post)) :
 ∃frontier : BitVec 64,let record:=scratchAllocationEnd scratch 280
 value=.val (.word record) ∧ HasGasFunding post record (childFunding gas) ∧
 post.memory (record+72)=.word stateGas ∧post.memory (record+208)=.word scratch ∧post.memory (record+224)=.word frame ∧
 post.globals=(s.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd frame 1024)))).update (ofString "scratch_ptr",.val (.word frontier)) ∧
 (allocationEnd frame 1024).toNat≤frontier.toNat ∧frontier.toNat≤record.toNat ∧record.toNat+280≤scratch.toNat ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (frameNewAt 0)
 rw [run] at metadata
 obtain ⟨afterMarks,marksRun,marksMemory,marksGlobals,marksDomain,marksEndian,marksCode⟩:=frame_new_marks_returned_context s post scratch frame value atScratch atFrame sourceCode run
 let marked:=frameNewMarksEntry s scratch frame
 have markedGlobals : marked.globals=s.globals:=rfl
 obtain ⟨zeroed,afterZero,zeroRun,zeroContext,zeroMemory,zeroGlobals,zeroDomain,zeroEndian,zeroCode⟩:=frame_new_zero_prefix_returned marked afterMarks scratch frame value atScratch atFrame (BitVec.le_def.mpr ordered) scratchCap sourceCode recordDomain marksRun
 let record:=scratchAllocationEnd scratch 280
 have zeroAtMark : zeroed.locals.lookup (ofString "stack_mark")=some (.val (.word scratch)) := by
  rw [zeroContext.otherLocals _ (by decide)]
  simp (config:={decide:=true}) [marked,frameNewMarksEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have zeroAtFrameMark : zeroed.locals.lookup (ofString "mem_mark")=some (.val (.word frame)) := by
  rw [zeroContext.otherLocals _ (by decide)]
  simp [marked,frameNewMarksEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have zeroScratch : zeroed.globals.lookup (ofString "scratch_ptr")=some (.val (.word record)) := by
  simp [zeroContext.globals,record,HolFiniteMapExact.lookup_update,FUPDATE]
 have zeroFrame : zeroed.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) := by
  rw [zeroContext.globals]
  change (marked.globals.update (ofString "scratch_ptr",.val (.word record))).lookup _=_
  rw [markedGlobals]
  simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atFrame
 obtain ⟨stacked,afterStack,stackRun,stackContext,stackMemory,stackGlobals,stackDomain,stackEndian,stackCode⟩:=frame_new_stack_prefix_returned zeroed afterZero record frame scratch value zeroContext.atRecord zeroAtMark zeroScratch zeroFrame (BitVec.le_def.mpr zeroContext.lower) (zeroContext.code.trans sourceCode) zeroRun
 let stack:=scratchAllocationEnd record 1024
 have stackAtRecord : stacked.locals.lookup (ofString "e")=some (.val (.word record)) := by rw [stackContext.otherLocals _ (by decide)];exact zeroContext.atRecord
 have stackAtFrameMark : stacked.locals.lookup (ofString "mem_mark")=some (.val (.word frame)) := by rw [stackContext.otherLocals _ (by decide)];exact zeroAtFrameMark
 have stackScratch : stacked.globals.lookup (ofString "scratch_ptr")=some (.val (.word stack)) := by simp [stackContext.globals,stack,HolFiniteMapExact.lookup_update,FUPDATE]
 have stackFrame : stacked.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) := by simpa (config:={decide:=true}) [stackContext.globals,HolFiniteMapExact.lookup_update,FUPDATE] using zeroFrame
 have stackCap : stack.toNat≤33806089496:=by
  have stackExtent:=stackContext.extent
  change stack.toNat+1024≤record.toNat at stackExtent
  have recordExtent:=zeroContext.extent
  change record.toNat+280≤scratch.toNat at recordExtent
  omega
 obtain ⟨ready,output,readyRun,memoryContext,memoryMemory,memoryGlobals,memoryDomain,memoryEndian,memoryCode⟩:=frame_new_memory_prefix_returned stacked afterStack record frame stack frame value stackAtRecord stackAtFrameMark stackScratch stackFrame stackContext.lower stackCap (stackContext.code.trans (zeroContext.code.trans sourceCode)) stackRun
 have readyAtRecord : ready.locals.lookup (ofString "e")=some (.val (.word record)) := by rw [memoryContext.otherLocals _ (by decide)];exact stackAtRecord
 have readyAtMessage : ready.locals.lookup (ofString "msg")=some (.val (.word message)) := by
  rw [memoryContext.otherLocals _ (by decide),stackContext.otherLocals _ (by decide),zeroContext.otherLocals _ (by decide)]
  simpa (config:={decide:=true}) [marked,frameNewMarksEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atMessage
 have readyGlobals : ready.globals=(s.globals.update (ofString "scratch_ptr",.val (.word stack))).update (ofString "frame_mem_ptr",.val (.word (allocationEnd frame 1024))) := by
  rw [memoryContext.globals,stackContext.globals,zeroContext.globals]
  change ((marked.globals.update (ofString "scratch_ptr",.val (.word record))).update (ofString "scratch_ptr",.val (.word stack))).update (ofString "frame_mem_ptr",.val (.word (allocationEnd frame 1024)))=_
  rw [markedGlobals]
  apply HolFiniteMapExact.ext
  funext key
  by_cases same : ofString "scratch_ptr"=key <;>simp [marked,frameNewMarksEntry,HolFiniteMapExact.lookup_update,FUPDATE,same]
 have messageFrame (offset : BitVec 64) (small : offset.toNat<176) : ready.memory (message+offset)=s.memory (message+offset) := by
  have recordBefore : record.toNat+280≤message.toNat:=zeroContext.extent.trans beforeMessage
  have separate (writeOffset : BitVec 64) (within : writeOffset.toNat<280) : message+offset≠record+writeOffset:=
   (frame_new_message_cell_separated record message writeOffset offset recordBefore messageBound within small).symm
  rw [memoryContext.memory,stackContext.memory]
  have n224:=separate 224 (by decide)
  have n24:=separate 24 (by decide)
  have n40:=separate 40 (by decide)
  have n208:=separate 208 (by decide)
  have n8:=separate 8 (by decide)
  have n232:=separate 232 (by decide)
  change message+offset≠record+224#64 at n224
  change message+offset≠record+24#64 at n24
  change message+offset≠record+40#64 at n40
  change message+offset≠record+208#64 at n208
  change message+offset≠record+8#64 at n8
  change message+offset≠record+232#64 at n232
  simp [storePlanMemory,List.foldl,n224,n24,n40,n208,n8,n232]
  change zeroed.memory (message+offset)=marked.memory (message+offset)
  apply zeroContext.upperMemory
  have bounded : message.toNat+offset.toNat<2^64:=by omega
  rw [BitVec.toNat_add_of_lt bounded]
  omega
 have readyContext : FrameNewTailContext ready record message codePointer codeLength accessAddresses accessSlots empty (allocationEnd frame 1024) stack := by
  constructor
  · exact readyAtRecord
  · exact readyAtMessage
  · simp (config:={decide:=true}) [readyGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [readyGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa (config:={decide:=true}) [readyGlobals,HolFiniteMapExact.lookup_update,FUPDATE] using atEmpty
  · exact memoryContext.upper
  · have bound:=stackContext.extent
    change stack.toNat+1024≤record.toNat at bound
    omega
  · have:=zeroContext.extent;change record.toNat+280≤scratch.toNat at this;omega
  · exact zeroContext.extent.trans beforeMessage
  · exact messageBound
  · intro offset member
    rw [memoryContext.domain,stackContext.domain,zeroContext.domain]
    exact messageDomain offset member
  · exact (messageFrame 112 (by decide)).trans codeAt
  · exact (messageFrame 120 (by decide)).trans lengthAt
  · exact (messageFrame 152 (by decide)).trans addressesAt
  · exact (messageFrame 160 (by decide)).trans slotsAt
  · exact lengthBound
  · exact memoryContext.code.trans (stackContext.code.trans (zeroContext.code.trans sourceCode))
 have used : ready.memory (record+184)=.word 0 := by
  rw [memoryContext.memory,stackContext.memory]
  simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 184 (by decide) (by decide)
 have spill : ready.memory (record+192)=.word 0 := by
  rw [memoryContext.memory,stackContext.memory]
  simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 192 (by decide) (by decide)
 have savedScratch : ready.memory (record+208)=.word scratch := by rw [memoryContext.memory,stackContext.memory];simp [storePlanMemory,List.foldl]
 have savedFrame : ready.memory (record+224)=.word frame := by rw [memoryContext.memory];simp [storePlanMemory,List.foldl]
 obtain ⟨frontier,returned,globals,lower,upper,funding,stateGasValue,scratchMark,frameMark,upperMemory,_,_,_⟩:=frame_new_copies_tail_returned_funding ready output record message codePointer codeLength accessAddresses accessSlots empty (allocationEnd frame 1024) stack gas stateGas scratch frame value readyContext
  ((messageFrame 40 (by decide)).trans gasAt) ((messageFrame 48 (by decide)).trans stateGasAt) used spill savedScratch savedFrame readyRun
 have finalMemory : post.memory=output.memory:=marksMemory.trans (zeroMemory.trans (stackMemory.trans memoryMemory))
 have finalGlobals : post.globals=output.globals:=marksGlobals.trans (zeroGlobals.trans (stackGlobals.trans memoryGlobals))
 refine ⟨frontier,returned,?_,?_,?_,?_,?_,lower,?_,zeroContext.extent,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · simpa only [HasGasFunding,finalMemory] using funding
 · rw [finalMemory];exact stateGasValue
 · rw [finalMemory];exact scratchMark
 · rw [finalMemory];exact frameMark
 · rw [finalGlobals,globals,readyGlobals]
   apply HolFiniteMapExact.ext
   funext key
   by_cases sp : ofString "scratch_ptr"=key <;>by_cases fm : ofString "frame_mem_ptr"=key <;>simp [HolFiniteMapExact.lookup_update,FUPDATE,sp,fm]
 · exact upper.trans readyContext.scratchBelow
 · intro watched beyond
   rw [finalMemory,upperMemory watched (zeroContext.extent.trans beyond)]
   rw [memoryContext.memory,stackContext.memory]
   have separate (offset : BitVec 64) (small : offset.toNat<280) : watched≠record+offset := by
    intro equal
    have bounded : record.toNat+offset.toNat<2^64:=by have:=readyContext.recordBound;omega
    have eqNat:=congrArg BitVec.toNat equal
    rw [BitVec.toNat_add_of_lt bounded] at eqNat
    have:=zeroContext.extent
    change record.toNat+280≤scratch.toNat at this
    omega
   have n224:=separate 224 (by decide)
   have n24:=separate 24 (by decide)
   have n40:=separate 40 (by decide)
   have n208:=separate 208 (by decide)
   have n8:=separate 8 (by decide)
   have n232:=separate 232 (by decide)
   change watched≠record+224#64 at n224
   change watched≠record+24#64 at n24
   change watched≠record+40#64 at n40
   change watched≠record+208#64 at n208
   change watched≠record+8#64 at n8
   change watched≠record+232#64 at n232
   simp [storePlanMemory,List.foldl,n224,n24,n40,n208,n8,n232]
   exact zeroContext.upperMemory watched beyond
#print axioms frame_new_whole_returned_funding
end InitECandidate.Runtime
