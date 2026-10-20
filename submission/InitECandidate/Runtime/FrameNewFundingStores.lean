import InitECandidate.Runtime.InterpreterFundingLayout
import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def frameNewAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_frame_new)
def frameNewLocalAddress (key : MlS) (offset : BitVec 64) : ExpHOL 64 :=
 .op .add [.var .local key,.const offset]
def frameNewFundingStores : ProgHOL 64 :=
 .seq (.store (frameNewLocalAddress (ofString "e") 64) (.load .one (frameNewLocalAddress (ofString "msg") 40)))
  (.seq (.store (frameNewLocalAddress (ofString "e") 72) (.load .one (frameNewLocalAddress (ofString "msg") 48))) .skip)

theorem frame_new_actual_funding_stores : frameNewAt 14=
 .seq (.store (frameNewLocalAddress (ofString "e") 64) (.load .one (frameNewLocalAddress (ofString "msg") 40)))
  (.seq (.store (frameNewLocalAddress (ofString "e") 72) (.load .one (frameNewLocalAddress (ofString "msg") 48))) (frameNewAt 16)) := rfl

private theorem frame_new_eval_address {F : Type} (s : PanSemStateFiniteExact 64 F)
 (key : MlS) (base offset : BitVec 64) (atBase : s.locals.lookup key=some (.val (.word base))) :
 @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (frameNewLocalAddress key offset)=
 some (.val (.word (base+offset))) := by
 simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,atBase,wordOpHOL,wordOp,valueIsWord,valueWord]

private theorem frame_new_eval_load {F : Type} (s : PanSemStateFiniteExact 64 F)
 (key : MlS) (base offset value : BitVec 64) (atBase : s.locals.lookup key=some (.val (.word base)))
 (readable : s.memaddrs (base+offset)) (atValue : s.memory (base+offset)=.word value) :
 @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
 (.load .one (frameNewLocalAddress key offset))=some (.val (.word value)) := by
 rw [evalHOLExact,frame_new_eval_address s key base offset atBase]
 simp [toExact,isWfShapeExactHOL,memLoadHOLExact,readable,atValue]

/-- Two nonwrapping, ordered actual frame/message records have disjoint cells. -/
theorem frame_new_message_cell_separated (frame message a b : BitVec 64)
 (before : frame.toNat+280≤message.toNat) (cap : message.toNat+176≤2^64)
 (aSmall : a.toNat<280) (bSmall : b.toNat<176) : frame+a≠message+b := by
 intro equal
 have fa : frame.toNat+a.toNat<2^64 := by omega
 have mb : message.toNat+b.toNat<2^64 := by omega
 have eq:=congrArg BitVec.toNat equal
 rw [BitVec.toNat_add_of_lt fa,BitVec.toNat_add_of_lt mb] at eq
 omega

/-- The original frame_new funding-store fragment initializes regular funding
from the real message cells, retaining the zeroed used/spill words. Its zeroed
cells are the interface consumed from the earlier actual memzero, not an
assumed callee execution or runtime bound. -/
theorem frame_new_funding_stores_initialize {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame message gas stateGas : BitVec 64)
 (atFrame : s.locals.lookup (ofString "e")=some (.val (.word frame)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (before : frame.toNat+280≤message.toNat) (cap : message.toNat+176≤2^64)
 (readFrame : ∀offset∈([64,72] : List (BitVec 64)),s.memaddrs (frame+offset))
 (readMessage : ∀offset∈([40,48] : List (BitVec 64)),s.memaddrs (message+offset))
 (messageGas : s.memory (message+40)=.word gas)
 (messageStateGas : s.memory (message+48)=.word stateGas)
 (zeroUsed : s.memory (frame+184)=.word 0) (zeroSpill : s.memory (frame+192)=.word 0) :
 ∃post,evaluateHOLFiniteState s frameNewFundingStores=(none,post) ∧
 HasGasFunding post frame (childFunding gas) ∧post.memory (frame+72)=.word stateGas ∧
 post.globals=s.globals ∧post.clock=s.clock ∧post.locals=s.locals ∧
 post.memaddrs=s.memaddrs ∧post.code=s.code ∧post.be=s.be ∧
 (∀watched,watched≠frame+64→watched≠frame+72→post.memory watched=s.memory watched) := by
 classical
 let first:=sourceWriteWord s (frame+64) gas
 let post:=sourceWriteWord first (frame+72) stateGas
 have one : evaluateHOLFiniteState s (.store (frameNewLocalAddress (ofString "e") 64)
  (.load .one (frameNewLocalAddress (ofString "msg") 40)))=(none,first) :=
  evaluate_store_word s _ _ _ _ (frame_new_eval_address s _ frame 64 atFrame)
   (frame_new_eval_load s _ message 40 gas atMessage (readMessage 40 (by simp)) messageGas) (readFrame 64 (by simp))
 have separate : message+48≠frame+64 :=
  (frame_new_message_cell_separated frame message 64 48 before cap (by decide) (by decide)).symm
 change message+48#64≠frame+64#64 at separate
 have stateGasKept : first.memory (message+48)=.word stateGas := by
  simpa [first,sourceWriteWord,separate] using messageStateGas
 have two : evaluateHOLFiniteState first (.store (frameNewLocalAddress (ofString "e") 72)
  (.load .one (frameNewLocalAddress (ofString "msg") 48)))=(none,post) :=
  evaluate_store_word first _ _ _ _ (frame_new_eval_address first _ frame 72 atFrame)
   (frame_new_eval_load first _ message 48 stateGas atMessage (readMessage 48 (by simp)) stateGasKept) (readFrame 72 (by simp))
 have finish : evaluateHOLFiniteState post .skip=(none,post) := evaluateHOLFiniteState_skip post
 refine ⟨post,evaluate_seq_none one (evaluate_seq_none two finish),?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
 · change s.memory (frame+184#64)=.word (0#64) at zeroUsed
   change s.memory (frame+192#64)=.word (0#64) at zeroSpill
   simp [HasGasFunding,childFunding,post,first,sourceWriteWord,zeroUsed,zeroSpill]
 · simp [post,sourceWriteWord]
 · intro watched ne64 ne72
   change watched≠frame+64#64 at ne64
   change watched≠frame+72#64 at ne72
   simp [post,first,sourceWriteWord,ne64,ne72]
#print axioms frame_new_actual_funding_stores
#print axioms frame_new_message_cell_separated
#print axioms frame_new_funding_stores_initialize
end InitECandidate.Runtime
