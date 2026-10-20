import InitECandidate.Runtime.FrameNewCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The original destruction-table store, access-pointer stores and both
count calls preserve every other record/old-memory word. -/
theorem frame_new_after_hash_tail_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message codePointer codeLength accessAddresses accessSlots empty frame scratch destruction watched : BitVec 64) (value : ValueHOL 64)
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (atDestruction : s.locals.lookup (ofString "del")=some (.val (.word destruction)))
 (separate : ∀offset∈([136,168,176,264,272,120,144,216] : List (BitVec 64)),watched≠record+offset)
 (run : evaluateHOLFiniteState s (frameNewAt 23)=(some (.returned value),post)) :
 value=.val (.word record) ∧post.globals=s.globals ∧post.memory watched=s.memory watched ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [source_frame_new_23] at run
 have oneRun:=frame_new_store_returned s post record 136 destruction (.var .local (ofString "del")) _ value valid.atRecord atDestruction run
 let one:=sourceWriteWord s (record+136) destruction
 have oneContext:=valid.after_record_write 136 destruction (by decide)
 change FrameNewTailContext one record message codePointer codeLength accessAddresses accessSlots empty frame scratch at oneContext
 have twoRun:=frame_new_load_store_returned one post record 168 message 152 accessAddresses (ofString "msg") _ value oneContext.atRecord oneContext.atMessage oneContext.addressesAt oneRun
 let two:=sourceWriteWord one (record+168) accessAddresses
 have twoContext:=oneContext.after_record_write 168 accessAddresses (by decide)
 change FrameNewTailContext two record message codePointer codeLength accessAddresses accessSlots empty frame scratch at twoContext
 have threeRun:=frame_new_load_store_returned two post record 176 message 160 accessSlots (ofString "msg") (frameNewAt 26) value twoContext.atRecord twoContext.atMessage twoContext.slotsAt twoRun
 let three:=sourceWriteWord two (record+176) accessSlots
 have threeContext:=twoContext.after_record_write 176 accessSlots (by decide)
 change FrameNewTailContext three record message codePointer codeLength accessAddresses accessSlots empty frame scratch at threeContext
 obtain ⟨returned,globals,memory,domain,endian,code⟩:=frame_new_count_tail_returned_frame three post record message codePointer codeLength accessAddresses accessSlots empty frame scratch watched value threeContext
  (by intro offset member;exact separate offset (by simp at member ⊢;tauto)) threeRun
 refine ⟨returned,globals,?_,domain,endian,code⟩
 have ne136:=separate 136 (by simp)
 have ne168:=separate 168 (by simp)
 have ne176:=separate 176 (by simp)
 change watched≠record+136#64 at ne136
 change watched≠record+168#64 at ne168
 change watched≠record+176#64 at ne176
 simpa [three,two,one,sourceWriteWord,ne136,ne168,ne176] using memory
#print axioms frame_new_after_hash_tail_returned_frame
end InitECandidate.Runtime
