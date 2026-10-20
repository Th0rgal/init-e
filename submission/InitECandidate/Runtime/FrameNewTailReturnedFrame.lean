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
theorem frame_new_tail_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message codePointer codeLength accessAddresses accessSlots empty frame scratch watched : BitVec 64) (value : ValueHOL 64)
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (above : record.toNat≤watched.toNat)
 (separate : ∀offset∈([80,88,104,112,136,168,176,264,272,120,144,216] : List (BitVec 64)),watched≠record+offset)
 (run : evaluateHOLFiniteState s (frameNewAt 16)=(some (.returned value),post)) :
 ∃frontier : BitVec 64,value=.val (.word record) ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word frontier)) ∧
 frame.toNat≤frontier.toNat ∧frontier.toNat≤scratch.toNat ∧
 post.memory watched=s.memory watched ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
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
 obtain ⟨returned,tailGlobals,tailMemory,_,_,_⟩:=frame_new_after_hash_tail_returned_frame third thirdOutput record message codePointer codeLength accessAddresses accessSlots empty frame frontier destruction watched value thirdContext atDestruction
  (by intro offset member;exact separate offset (by simp at member ⊢;tauto)) thirdRun
 have firstUpper : firstFrontier.toNat≤record.toNat:=firstContext.scratchBelow
 have secondUpper : secondFrontier.toNat≤record.toNat:=secondContext.scratchBelow
 have ne80:=separate 80 (by simp)
 change watched≠record+80#64 at ne80
 refine ⟨frontier,returned,?_,thirdContext.ordered,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [firstScope,secondScope,thirdScope]
   change thirdOutput.globals=_
   rw [tailGlobals,thirdGlobals]
   change (second.globals.update (ofString "scratch_ptr",.val (.word frontier)))=_
   rw [secondGlobals]
   change ((first.globals.update (ofString "scratch_ptr",.val (.word secondFrontier))).update (ofString "scratch_ptr",.val (.word frontier)))=_
   rw [firstGlobals]
   apply HolFiniteMapExact.ext
   funext key
   by_cases same : ofString "scratch_ptr"=key <;>simp [HolFiniteMapExact.lookup_update,FUPDATE,same]
 · exact (thirdBeforeDestruction.trans destructionBeforeSecond).trans ((secondBeforeLogs.trans logsBeforeFirst).trans (firstBeforeBitmap.trans bitmapBeforeScratch))
 · rw [firstScope,secondScope,thirdScope]
   change thirdOutput.memory watched=_
   rw [tailMemory,thirdMemory watched (secondUpper.trans above)]
   change (frameNewLogsPost second record logs message).memory watched=_
   rw [frame_new_logs_stores_word_frame second record logs message watched (by intro offset member;exact separate offset (by simp at member ⊢;tauto))]
   rw [secondMemory watched (firstUpper.trans above)]
   change (sourceWriteWord first (record+80) bitmap).memory watched=_
   change (if watched=record+80#64 then .word bitmap else first.memory watched)=_
   rw [if_neg ne80]
   exact firstMemory watched (valid.scratchBelow.trans above)
#print axioms frame_new_tail_returned_frame
end InitECandidate.Runtime
