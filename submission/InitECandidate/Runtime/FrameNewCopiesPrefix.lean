import InitECandidate.Runtime.FrameNewStoreReturned
import InitECandidate.Runtime.GasFunding
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def frameNewCopiesPost {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record code length gas stateGas : BitVec 64) : PanSemStateFiniteExact 64 F :=
 sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord s (record+48) code) (record+56) length) (record+64) gas) (record+72) stateGas

/-- Four actual frame_new message copies. Readability of all source/destination
cells follows from the successful returned original path, not a caller premise. -/
theorem frame_new_copies_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message code length gas stateGas : BitVec 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (before : record.toNat+280≤message.toNat) (cap : message.toNat+176≤2^64)
 (atCode : s.memory (message+112)=.word code) (atLength : s.memory (message+120)=.word length)
 (atGas : s.memory (message+40)=.word gas) (atStateGas : s.memory (message+48)=.word stateGas)
 (run : evaluateHOLFiniteState s (frameNewAt 12)=(some (.returned value),post)) :
 evaluateHOLFiniteState (frameNewCopiesPost s record code length gas stateGas) (frameNewAt 16)=(some (.returned value),post) := by
 have separate : ∀a∈([48#64,56#64,64#64] : List (BitVec 64)),∀b∈([120#64,40#64,48#64] : List (BitVec 64)),message+b≠record+a := by
  intro a aMember b bMember
  apply (frame_new_message_cell_separated record message a b before cap _ _).symm
  · simp at aMember
    rcases aMember with rfl|rfl|rfl <;>decide
  · simp at bMember
    rcases bMember with rfl|rfl|rfl <;>decide
 have source12 : frameNewAt 12=.seq (.store (frameNewLocalAddress (ofString "e") 48)
  (.load .one (frameNewLocalAddress (ofString "msg") 112))) (frameNewAt 13) := rfl
 have source13 : frameNewAt 13=.seq (.store (frameNewLocalAddress (ofString "e") 56)
  (.load .one (frameNewLocalAddress (ofString "msg") 120))) (frameNewAt 14) := rfl
 have source14 : frameNewAt 14=.seq (.store (frameNewLocalAddress (ofString "e") 64)
  (.load .one (frameNewLocalAddress (ofString "msg") 40))) (frameNewAt 15) := rfl
 have source15 : frameNewAt 15=.seq (.store (frameNewLocalAddress (ofString "e") 72)
  (.load .one (frameNewLocalAddress (ofString "msg") 48))) (frameNewAt 16) := rfl
 rw [source12] at run
 have run1:=frame_new_load_store_returned s post record 48 message 112 code (ofString "msg") (frameNewAt 13) value atRecord atMessage atCode run
 let one:=sourceWriteWord s (record+48) code
 change evaluateHOLFiniteState one (frameNewAt 13)=_ at run1
 have lengthKept : one.memory (message+120)=.word length := by
  have ne:=separate (48#64) (by simp) (120#64) (by simp)
  simpa [one,sourceWriteWord,ne] using atLength
 rw [source13] at run1
 have run2:=frame_new_load_store_returned one post record 56 message 120 length (ofString "msg") (frameNewAt 14) value atRecord atMessage lengthKept run1
 let two:=sourceWriteWord one (record+56) length
 change evaluateHOLFiniteState two (frameNewAt 14)=_ at run2
 have gasKept : two.memory (message+40)=.word gas := by
  have a:=separate (48#64) (by simp) (40#64) (by simp)
  have b:=separate (56#64) (by simp) (40#64) (by simp)
  simpa [two,one,sourceWriteWord,a,b] using atGas
 rw [source14] at run2
 have run3:=frame_new_load_store_returned two post record 64 message 40 gas (ofString "msg") (frameNewAt 15) value atRecord atMessage gasKept run2
 let three:=sourceWriteWord two (record+64) gas
 change evaluateHOLFiniteState three (frameNewAt 15)=_ at run3
 have stateGasKept : three.memory (message+48)=.word stateGas := by
  have a:=separate (48#64) (by simp) (48#64) (by simp)
  have b:=separate (56#64) (by simp) (48#64) (by simp)
  have c:=separate (64#64) (by simp) (48#64) (by simp)
  simpa [three,two,one,sourceWriteWord,a,b,c] using atStateGas
 rw [source15] at run3
 exact frame_new_load_store_returned three post record 72 message 48 stateGas (ofString "msg") (frameNewAt 16) value atRecord atMessage stateGasKept run3

/-- The actual copy endpoint initializes fresh regular funding; neither copy
can alter the zeroed used/spill words. -/
theorem frame_new_copies_funding {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record code length gas stateGas : BitVec 64)
 (zeroUsed : s.memory (record+184)=.word 0) (zeroSpill : s.memory (record+192)=.word 0) :
 HasGasFunding (frameNewCopiesPost s record code length gas stateGas) record (childFunding gas) ∧
 (frameNewCopiesPost s record code length gas stateGas).memory (record+72)=.word stateGas := by
 change s.memory (record+184#64)=.word (0#64) at zeroUsed
 change s.memory (record+192#64)=.word (0#64) at zeroSpill
 simp [frameNewCopiesPost,HasGasFunding,childFunding,sourceWriteWord,zeroUsed,zeroSpill]

#print axioms frame_new_copies_returned
#print axioms frame_new_copies_funding
end InitECandidate.Runtime
