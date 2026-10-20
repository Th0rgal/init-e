import InitECandidate.Runtime.FrameNewStoreReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

noncomputable def frameNewFinalStorePost {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record count empty : BitVec 64) : PanSemStateFiniteExact 64 F :=
 sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord s (record+272) count) (record+120) empty) (record+144) empty) (record+216) 0

/-- The final original constructor stores and return have an exact endpoint.
The global evm_empty is explicitly scalar, as established by real startup. -/
theorem frame_new_final_stores_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record count empty : BitVec 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (atCount : s.locals.lookup (ofString "acc_n")=some (.val (.word count)))
 (atEmpty : s.globals.lookup (ofString "evm_empty")=some (.val (.word empty)))
 (run : evaluateHOLFiniteState s (frameNewAt 29)=(some (.returned value),post)) :
 value=.val (.word record) ∧post=emptyLocalsHOLFinite (frameNewFinalStorePost s record count empty) := by
 have source29 : frameNewAt 29=.seq (.store (frameNewLocalAddress (ofString "e") 272) (.var .local (ofString "acc_n"))) (frameNewAt 30) := rfl
 have source30 : frameNewAt 30=.seq (.store (frameNewLocalAddress (ofString "e") 120) (.var .global (ofString "evm_empty"))) (frameNewAt 31) := rfl
 have source31 : frameNewAt 31=.seq (.store (frameNewLocalAddress (ofString "e") 144) (.var .global (ofString "evm_empty"))) (frameNewAt 32) := rfl
 have source32 : frameNewAt 32=.seq (.store (frameNewLocalAddress (ofString "e") 216) (.const 0)) (frameNewAt 33) := rfl
 rw [source29] at run
 have oneRun:=frame_new_store_returned s post record 272 count (.var .local (ofString "acc_n")) (frameNewAt 30) value atRecord atCount run
 let one:=sourceWriteWord s (record+272) count
 change evaluateHOLFiniteState one (frameNewAt 30)=_ at oneRun
 rw [source30] at oneRun
 have twoRun:=frame_new_store_returned one post record 120 empty (.var .global (ofString "evm_empty")) (frameNewAt 31) value atRecord atEmpty oneRun
 let two:=sourceWriteWord one (record+120) empty
 change evaluateHOLFiniteState two (frameNewAt 31)=_ at twoRun
 rw [source31] at twoRun
 have threeRun:=frame_new_store_returned two post record 144 empty (.var .global (ofString "evm_empty")) (frameNewAt 32) value atRecord atEmpty twoRun
 let three:=sourceWriteWord two (record+144) empty
 change evaluateHOLFiniteState three (frameNewAt 32)=_ at threeRun
 rw [source32] at threeRun
 have fourRun:=frame_new_store_returned three post record 216 0 (.const 0) (frameNewAt 33) value atRecord rfl threeRun
 let finalState:=frameNewFinalStorePost s record count empty
 have returned : evaluateHOLFiniteState finalState (frameNewAt 33)=
  (some (.returned (.val (.word record))),emptyLocalsHOLFinite finalState) := by
  rw [source_frame_new_33]
  simp [evaluateHOLFiniteState_return,evalHOLExact,show finalState.locals.lookup (ofString "e")=some (.val (.word record)) from atRecord,shapeOfHOLExact]
 obtain ⟨resultEq,postEq⟩:=Prod.mk.inj (fourRun.symm.trans returned)
 exact ⟨PanSemResultExact.returned.inj (Option.some.inj resultEq),postEq⟩

theorem frame_new_final_stores_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record count empty watched : BitVec 64)
 (separate : ∀offset∈([272,120,144,216] : List (BitVec 64)),watched≠record+offset) :
 (frameNewFinalStorePost s record count empty).memory watched=s.memory watched := by
 have a:=separate 272 (by simp)
 have b:=separate 120 (by simp)
 have c:=separate 144 (by simp)
 have d:=separate 216 (by simp)
 change watched≠record+272#64 at a
 change watched≠record+120#64 at b
 change watched≠record+144#64 at c
 change watched≠record+216#64 at d
 simp [frameNewFinalStorePost,sourceWriteWord,a,b,c,d]
#print axioms frame_new_final_stores_returned
#print axioms frame_new_final_stores_word_frame
end InitECandidate.Runtime
