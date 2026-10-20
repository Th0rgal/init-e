import InitECandidate.Runtime.FrameNewTailCountContext
import InitECandidate.Runtime.FrameNewFinalStores
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Both actual htab_count calls, their real local assignment, all final
record stores and the original return preserve protected funding/old words. -/
theorem frame_new_count_tail_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message codePointer codeLength accessAddresses accessSlots empty frame scratch watched : BitVec 64) (value : ValueHOL 64)
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (separate : ∀offset∈([264,272,120,144,216] : List (BitVec 64)),watched≠record+offset)
 (run : evaluateHOLFiniteState s (frameNewAt 26)=(some (.returned value),post)) :
 value=.val (.word record) ∧post.globals=s.globals ∧post.memory watched=s.memory watched ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (frameNewAt 26)
 rw [run] at metadata
 rw [source_frame_new_26] at run
 have args:=valid.message_load_arguments 152 accessAddresses (by simp) valid.addressesAt
 obtain ⟨count,ready,output,tailRun,postEq,context,atCount,memory,globals⟩:=
  valid.count_declaration_returned post (ofString "acc_n") _ (frameNewAt 27) accessAddresses value (by decide) (by decide) args run
 rw [source_frame_new_27] at tailRun
 have nextRun:=frame_new_store_returned ready output record 264 count (.var .local (ofString "acc_n")) (frameNewAt 28) value context.atRecord atCount tailRun
 let one:=sourceWriteWord ready (record+264) count
 have oneContext:=context.after_record_write 264 count (by decide)
 change FrameNewTailContext one record message codePointer codeLength accessAddresses accessSlots empty frame scratch at oneContext
 change evaluateHOLFiniteState one (frameNewAt 28)=_ at nextRun
 rw [source_frame_new_28] at nextRun
 obtain ⟨assigned,normal,finishRun⟩:=encode_header_seq_returned_of_no_return one output _ _ value
  (fun v=>evaluate_noDirectReturn _ (by decide_cbv) one v) nextRun
 have args2:=oneContext.message_load_arguments 160 accessSlots (by simp) oneContext.slotsAt
 obtain ⟨slotCount,atSlotCount,assignedContext,assignedMemory,assignedGlobals⟩:=
  oneContext.count_assignment_normal assigned (ofString "acc_n") _ accessSlots (by decide) (by decide) args2 normal
 obtain ⟨returned,outputEq⟩:=frame_new_final_stores_returned assigned output record slotCount empty value assignedContext.atRecord atSlotCount assignedContext.atEmpty finishRun
 refine ⟨returned,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [postEq,outputEq]
   exact assignedGlobals.trans globals
 · rw [postEq,outputEq]
   change (frameNewFinalStorePost assigned record slotCount empty).memory watched=_
   rw [frame_new_final_stores_word_frame assigned record slotCount empty watched (by intro offset member;exact separate offset (by simp at member ⊢;tauto))]
   rw [assignedMemory]
   have ne:=separate 264 (by simp)
   change watched≠record+264#64 at ne
   simpa [one,sourceWriteWord,ne] using congrFun memory watched
#print axioms frame_new_count_tail_returned_frame
end InitECandidate.Runtime
