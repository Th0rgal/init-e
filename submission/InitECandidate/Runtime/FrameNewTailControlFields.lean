import InitECandidate.Runtime.FrameNewAfterHashTail
import InitECandidate.Runtime.FrameNewLogsStores
import InitECandidate.Runtime.FrameNewTailScratchContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Actual remaining frame constructor, including its three concrete scratch
constructors. This frames saved release marks and all four funding words. -/
theorem frame_new_tail_returned_control_fields {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64) (value : ValueHOL 64)
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (run : evaluateHOLFiniteState s (frameNewAt 16)=(some (.returned value),post)) :
 post.memory (record+104)=.word 1 ∧post.memory (record+112)=.word message := by
 have metadata:=evaluateHOLFiniteState_metadata s (frameNewAt 16)
 rw [run] at metadata
 rw [source_frame_new_16] at run
 obtain ⟨bitmap,firstFrontier,first,firstOutput,firstRun,firstScope,firstContext,atBitmap,firstGlobals,firstBeforeBitmap,bitmapBeforeScratch,firstMemory⟩:=
  valid.scratch_returned (.bitmap codePointer codeLength) post (ofString "jd") _ _ (frameNewAt 17) value (by decide) (by decide) valid.bitmap_arguments valid.lengthBound run
 rw [source_frame_new_17] at firstRun
 have logsRun:=frame_new_store_returned first firstOutput record 80 bitmap (.var .local (ofString "jd")) (frameNewAt 18) value firstContext.atRecord atBitmap firstRun
 let stored:=sourceWriteWord first (record+80) bitmap
 have storedContext:=firstContext.after_record_write 80 bitmap (by decide)
 change FrameNewTailContext stored record message codePointer codeLength accessAddresses accessSlots empty frame firstFrontier at storedContext
 rw [source_frame_new_18] at logsRun
 obtain ⟨logs,secondFrontier,second,secondOutput,secondRun,secondScope,secondContext,atLogs,secondGlobals,secondBeforeLogs,logsBeforeFirst,secondMemory⟩:=
  storedContext.scratch_returned .logs firstOutput (ofString "logs") (.const 8) (.const 4) (frameNewAt 19) value (by decide) (by decide) rfl trivial logsRun
 have destructionRun:=frame_new_logs_stores_returned second secondOutput record message logs value secondContext.atRecord secondContext.atMessage atLogs secondRun
 let logsStored:=frameNewLogsPost second record logs message
 have logsContext:=secondContext.after_logs_stores logs
 change FrameNewTailContext logsStored record message codePointer codeLength accessAddresses accessSlots empty frame secondFrontier at logsContext
 rw [source_frame_new_22] at destructionRun
 obtain ⟨destruction,frontier,third,thirdOutput,thirdRun,thirdScope,thirdContext,atDestruction,thirdGlobals,thirdBeforeDestruction,destructionBeforeSecond,thirdMemory⟩:=
  logsContext.scratch_returned .destruction secondOutput (ofString "del") (.const 20) (.const 4) (frameNewAt 23) value (by decide) (by decide) rfl trivial destructionRun
 have wordAbove (offset : BitVec 64) (small : offset.toNat<280) : secondFrontier.toNat≤(record+offset).toNat := by
  have nowrap : record.toNat+offset.toNat<2^64:=by have:=valid.recordBound;omega
  rw [BitVec.toNat_add_of_lt nowrap]
  have:=secondContext.scratchBelow
  omega
 have kept (offset : BitVec 64) (member : offset∈([104,112] : List (BitVec 64))) :
 post.memory (record+offset)=(frameNewLogsPost second record logs message).memory (record+offset) := by
  have small : offset.toNat<280:=by simp at member;rcases member with rfl|rfl <;>decide
  have separated : ∀written∈([136,168,176,264,272,120,144,216] : List (BitVec 64)),record+offset≠record+written := by
   intro written present
   simp at member present
   rcases member with rfl|rfl <;>rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>simp
  obtain ⟨_,_,memory,_,_,_⟩:=frame_new_after_hash_tail_returned_frame third thirdOutput record message codePointer codeLength accessAddresses accessSlots empty frame frontier destruction (record+offset) value thirdContext atDestruction separated thirdRun
  rw [firstScope,secondScope,thirdScope]
  change thirdOutput.memory (record+offset)=_
  exact memory.trans (thirdMemory (record+offset) (wordAbove offset small))
 constructor
 · have kept104:=kept 104 (by simp)
   simpa [frameNewLogsPost,sourceWriteWord] using kept104
 · have kept112:=kept 112 (by simp)
   simpa [frameNewLogsPost,sourceWriteWord] using kept112
#print axioms frame_new_tail_returned_control_fields
end InitECandidate.Runtime
