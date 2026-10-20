import InitECandidate.Runtime.FrameOpenSource
import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def frameOpenFinalPost {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record parent previous kind message child : BitVec 64) : PanSemStateFiniteExact 64 F:=
 setKvarHOLFinite .global (ofString "cur_cont") (.val (.word record))
 (setKvarHOLFinite .global (ofString "ev") (.val (.word child))
 (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord s (record+0) parent) (record+8) previous) (record+16) kind) (record+40) message))

/-- Exact original continuation-link stores and current-frame assignments.
No successful-store or global-assignment-validity callback is assumed. -/
theorem frame_open_final_stores_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record parent previous kind message child : BitVec 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "rec")=some (.val (.word record)))
 (atParent : s.locals.lookup (ofString "parent")=some (.val (.word parent)))
 (atPrevious : s.globals.lookup (ofString "cur_cont")=some (.val (.word previous)))
 (atKind : s.locals.lookup (ofString "kind")=some (.val (.word kind)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (run : evaluateHOLFiniteState s (frameOpenAt 4)=(some (.returned value),post)) :
 value=.val (.word child) ∧post=emptyLocalsHOLFinite (frameOpenFinalPost s record parent previous kind message child) := by
 rw [source_frame_open_4] at run
 have firstRun:=funding_store_returned_context s post (frameNewLocalAddress (ofString "rec") 0) (.var .local (ofString "parent")) (record+0) parent _ value
  (eval_frame_new_local_address s (ofString "rec") record 0 atRecord) atParent run
 let one:=sourceWriteWord s (record+0) parent
 have secondRun:=funding_store_returned_context one post (frameNewLocalAddress (ofString "rec") 8) (.var .global (ofString "cur_cont")) (record+8) previous _ value
  (eval_frame_new_local_address one (ofString "rec") record 8 atRecord) atPrevious firstRun
 let two:=sourceWriteWord one (record+8) previous
 have thirdRun:=funding_store_returned_context two post (frameNewLocalAddress (ofString "rec") 16) (.var .local (ofString "kind")) (record+16) kind _ value
  (eval_frame_new_local_address two (ofString "rec") record 16 atRecord) atKind secondRun
 let three:=sourceWriteWord two (record+16) kind
 have fourthRun:=funding_store_returned_context three post (frameNewLocalAddress (ofString "rec") 40) (.var .local (ofString "msg")) (record+40) message (frameOpenAt 8) value
  (eval_frame_new_local_address three (ofString "rec") record 40 atRecord) atMessage thirdRun
 let four:=sourceWriteWord three (record+40) message
 change evaluateHOLFiniteState four (frameOpenAt 8)=_ at fourthRun
 rw [source_frame_open_8] at fourthRun
 have fifthRun:=funding_assignment_returned_context four post .global (ofString "ev") (.var .local (ofString "child")) child _ value atChild fourthRun
 let five:=setKvarHOLFinite .global (ofString "ev") (.val (.word child)) four
 have sixthRun:=funding_assignment_returned_context five post .global (ofString "cur_cont") (.var .local (ofString "rec")) record (.return (.var .local (ofString "child"))) value atRecord fifthRun
 let finalState:=frameOpenFinalPost s record parent previous kind message child
 have returned : evaluateHOLFiniteState finalState (.return (.var .local (ofString "child")))=(some (.returned (.val (.word child))),emptyLocalsHOLFinite finalState) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,show finalState.locals.lookup (ofString "child")=some (.val (.word child)) from atChild,shapeOfHOLExact]
 obtain ⟨returnedEq,postEq⟩:=Prod.mk.inj (sixthRun.symm.trans returned)
 exact ⟨PanSemResultExact.returned.inj (Option.some.inj returnedEq),postEq⟩

theorem frame_open_final_stores_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record parent previous kind message child watched : BitVec 64)
 (different : ∀offset∈([0,8,16,40] : List (BitVec 64)),watched≠record+offset) :
 (frameOpenFinalPost s record parent previous kind message child).memory watched=s.memory watched := by
 have n0:=different 0 (by simp)
 have n8:=different 8 (by simp)
 have n16:=different 16 (by simp)
 have n40:=different 40 (by simp)
 change watched≠record+0#64 at n0
 change watched≠record+8#64 at n8
 change watched≠record+16#64 at n16
 change watched≠record+40#64 at n40
 simp only [BitVec.add_zero] at n0
 simp [frameOpenFinalPost,setKvarHOLFinite,setGlobalHOLFinite,sourceWriteWord,n0,n8,n16,n40]
#print axioms frame_open_final_stores_returned
#print axioms frame_open_final_stores_word_frame
end InitECandidate.Runtime
