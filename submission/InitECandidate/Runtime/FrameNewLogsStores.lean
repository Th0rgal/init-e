import InitECandidate.Runtime.FrameNewTailContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def frameNewLogsPost {F : Type} (s : PanSemStateFiniteExact 64 F) (record logs message : BitVec 64) :=
 sourceWriteWord (sourceWriteWord (sourceWriteWord s (record+88) logs) (record+104) 1) (record+112) message

theorem frame_new_logs_stores_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message logs : BitVec 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (atLogs : s.locals.lookup (ofString "logs")=some (.val (.word logs)))
 (run : evaluateHOLFiniteState s (frameNewAt 19)=(some (.returned value),post)) :
 evaluateHOLFiniteState (frameNewLogsPost s record logs message) (frameNewAt 22)=(some (.returned value),post) := by
 rw [source_frame_new_19] at run
 have first:=frame_new_store_returned s post record 88 logs (.var .local (ofString "logs")) _ value atRecord atLogs run
 have second:=frame_new_store_returned (sourceWriteWord s (record+88) logs) post record 104 1 (.const 1) _ value atRecord rfl first
 exact frame_new_store_returned (sourceWriteWord (sourceWriteWord s (record+88) logs) (record+104) 1) post record 112 message (.var .local (ofString "msg")) (frameNewAt 22) value atRecord atMessage second

theorem FrameNewTailContext.after_logs_stores {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (logs : BitVec 64) : FrameNewTailContext (frameNewLogsPost s record logs message) record message codePointer codeLength accessAddresses accessSlots empty frame scratch :=
 ((valid.after_record_write 88 logs (by decide)).after_record_write 104 1 (by decide)).after_record_write 112 message (by decide)

theorem frame_new_logs_stores_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record logs message watched : BitVec 64)
 (separate : ∀offset∈([88,104,112] : List (BitVec 64)),watched≠record+offset) :
 (frameNewLogsPost s record logs message).memory watched=s.memory watched := by
 have n88:=separate 88 (by simp)
 have n104:=separate 104 (by simp)
 have n112:=separate 112 (by simp)
 change watched≠record+88#64 at n88
 change watched≠record+104#64 at n104
 change watched≠record+112#64 at n112
 simp [frameNewLogsPost,sourceWriteWord,n88,n104,n112]
#print axioms frame_new_logs_stores_returned
#print axioms FrameNewTailContext.after_logs_stores
#print axioms frame_new_logs_stores_word_frame
end InitECandidate.Runtime
