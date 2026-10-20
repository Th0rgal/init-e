import InitECandidate.Runtime.FrameNewCopiesTailReturnedFunding
import InitECandidate.Runtime.FrameNewTailControlFields
import InitECandidate.Runtime.FrameNewMarksReturnedContext
import InitECandidate.Runtime.FrameNewZeroPrefix
import InitECandidate.Runtime.FrameNewStackPrefix
import InitECandidate.Runtime.FrameNewMemoryPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Concrete initial operand/code/control state in the actual280-byte EVM frame.
This seed makes no claim about future opcode preservation. -/
structure FrameNewPhysicalSeed {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record scratch frame codePointer codeLength message : BitVec 64) : Prop where
 extent : record.toNat+280≤scratch.toNat
 aligned : record.toNat%8=0
 stackExtent : (scratchAllocationEnd record 1024).toNat+1024≤record.toNat
 memoryExtent : frame.toNat+1024≤(allocationEnd frame 1024).toNat
 memoryBeforeStack : (allocationEnd frame 1024).toNat≤(scratchAllocationEnd record 1024).toNat
 stackAt : s.memory (record+8)=.word (scratchAllocationEnd record 1024)
 stackSizeAt : s.memory (record+16)=.word 0
 memoryAt : s.memory (record+24)=.word frame
 memorySizeAt : s.memory (record+32)=.word 0
 memoryCapacityAt : s.memory (record+40)=.word 1024
 codeAt : s.memory (record+48)=.word codePointer
 codeLengthAt : s.memory (record+56)=.word codeLength
 activeAt : s.memory (record+104)=.word 1
 messageAt : s.memory (record+112)=.word message
 returnSizeAt : s.memory (record+128)=.word 0
 errorAt : s.memory (record+160)=.word 0
 stateUsedAt : s.memory (record+200)=.word 0
 stackCapacityAt : s.memory (record+232)=.word 32

/-- Every initial physical seed field is derived from the whole original
frame constructor, using its actual returned path and actual callees. -/
theorem frame_new_whole_returned_physical_seed {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
 FrameNewPhysicalSeed post (scratchAllocationEnd scratch 280) scratch frame codePointer codeLength message := by
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
 let copied:=frameNewCopiesPost ready record codePointer codeLength gas stateGas
 have copiedContext:=readyContext.after_copies gas stateGas
 have tailRun:=frame_new_copies_returned ready output record message codePointer codeLength gas stateGas value readyContext.atRecord readyContext.atMessage readyContext.beforeMessage readyContext.messageBound readyContext.codeAt readyContext.lengthAt ((messageFrame 40 (by decide)).trans gasAt) ((messageFrame 48 (by decide)).trans stateGasAt) readyRun
 have endpointMemory : post.memory=output.memory:=marksMemory.trans (zeroMemory.trans (stackMemory.trans memoryMemory))
 have copiedMemory : copied.memory=storePlanMemory zeroed.memory
  [(record+208,scratch),(record+8,stack),(record+232,32),(record+224,frame),(record+24,frame),(record+40,1024),(record+48,codePointer),(record+56,codeLength),(record+64,gas),(record+72,stateGas)] := by
  funext address
  simp only [copied,frameNewCopiesPost,sourceWriteWord]
  rw [memoryContext.memory,stackContext.memory]
  rfl
 have kept (offset : BitVec 64) (member : offset∈([8,16,24,32,40,48,56,128,160,200,232] : List (BitVec 64))) : post.memory (record+offset)=copied.memory (record+offset) := by
  have small : offset.toNat<280:=by simp at member;rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>decide
  have above : record.toNat≤(record+offset).toNat := by
   have bound : record.toNat+offset.toNat<2^64:=by have:=readyContext.recordBound;omega
   rw [BitVec.toNat_add_of_lt bound]
   omega
  have separate : ∀written∈([80,88,104,112,136,168,176,264,272,120,144,216] : List (BitVec 64)),record+offset≠record+written := by
   intro written present
   simp at member present
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>simp
  obtain ⟨_,_,_,_,_,wordFrame,_,_,_⟩:=frame_new_tail_returned_frame copied output record message codePointer codeLength accessAddresses accessSlots empty (allocationEnd frame 1024) stack (record+offset) value copiedContext above separate tailRun
  exact (congrFun endpointMemory (record+offset)).trans wordFrame
 have control:=frame_new_tail_returned_control_fields copied output record message codePointer codeLength accessAddresses accessSlots empty (allocationEnd frame 1024) stack value copiedContext tailRun
 constructor
 · exact zeroContext.extent
 · exact scratchAllocationEnd_mask_aligned scratch 280
 · exact stackContext.extent
 · exact memoryContext.coverage
 · exact memoryContext.upper
 · rw [kept 8 (by simp),copiedMemory]
   simp [storePlanMemory,List.foldl,stack,record]
 · rw [kept 16 (by simp),copiedMemory]
   simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 16 (by decide) (by decide)
 · rw [kept 24 (by simp),copiedMemory]
   simp [storePlanMemory,List.foldl]
 · rw [kept 32 (by simp),copiedMemory]
   simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 32 (by decide) (by decide)
 · rw [kept 40 (by simp),copiedMemory]
   simp [storePlanMemory,List.foldl]
 · rw [kept 48 (by simp),copiedMemory]
   simp [storePlanMemory,List.foldl]
 · rw [kept 56 (by simp),copiedMemory]
   simp [storePlanMemory,List.foldl]
 · rw [endpointMemory]
   exact control.1
 · rw [endpointMemory]
   exact control.2
 · rw [kept 128 (by simp),copiedMemory]
   simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 128 (by decide) (by decide)
 · rw [kept 160 (by simp),copiedMemory]
   simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 160 (by decide) (by decide)
 · rw [kept 200 (by simp),copiedMemory]
   simpa [storePlanMemory,List.foldl,record] using zeroContext.zeroWords 200 (by decide) (by decide)
 · rw [kept 232 (by simp),copiedMemory]
   simp [storePlanMemory,List.foldl]
#print axioms frame_new_whole_returned_physical_seed
end InitECandidate.Runtime
