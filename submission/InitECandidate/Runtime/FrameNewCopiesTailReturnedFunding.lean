import InitECandidate.Runtime.FrameNewTailReturnedFrame
import InitECandidate.Runtime.FrameNewCopiesPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem FrameNewTailContext.after_copies {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (gas stateGas : BitVec 64) : FrameNewTailContext (frameNewCopiesPost s record codePointer codeLength gas stateGas)
 record message codePointer codeLength accessAddresses accessSlots empty frame scratch :=
 (((valid.after_record_write 48 codePointer (by decide)).after_record_write 56 codeLength (by decide)).after_record_write 64 gas (by decide)).after_record_write 72 stateGas (by decide)

/-- Real original copies and remaining constructor establish fresh funding
and preserve the two actual saved workspace marks. No successful callee is
provided as a premise. -/
theorem frame_new_copies_tail_returned_funding {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record message codePointer codeLength accessAddresses accessSlots empty frame scratch gas stateGas scratchMark frameMark : BitVec 64) (value : ValueHOL 64)
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (atGas : s.memory (message+40)=.word gas) (atStateGas : s.memory (message+48)=.word stateGas)
 (zeroUsed : s.memory (record+184)=.word 0) (zeroSpill : s.memory (record+192)=.word 0)
 (savedScratch : s.memory (record+208)=.word scratchMark) (savedFrame : s.memory (record+224)=.word frameMark)
 (run : evaluateHOLFiniteState s (frameNewAt 12)=(some (.returned value),post)) :
 ∃frontier : BitVec 64,value=.val (.word record) ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word frontier)) ∧
 frame.toNat≤frontier.toNat ∧frontier.toNat≤scratch.toNat ∧
 HasGasFunding post record (childFunding gas) ∧post.memory (record+72)=.word stateGas ∧
 post.memory (record+208)=.word scratchMark ∧post.memory (record+224)=.word frameMark ∧
 (∀watched : BitVec 64,record.toNat+280≤watched.toNat → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 let copied:=frameNewCopiesPost s record codePointer codeLength gas stateGas
 have copiedContext:=valid.after_copies gas stateGas
 have tailRun:=frame_new_copies_returned s post record message codePointer codeLength gas stateGas value valid.atRecord valid.atMessage valid.beforeMessage valid.messageBound valid.codeAt valid.lengthAt atGas atStateGas run
 have wordAbove (offset : BitVec 64) (small : offset.toNat<280) : record.toNat≤(record+offset).toNat := by
  have bounded : record.toNat+offset.toNat<2^64:=by have:=valid.recordBound;omega
  rw [BitVec.toNat_add_of_lt bounded]
  omega
 have fundingSeparate : ∀offset∈([64,72,184,192,208,224] : List (BitVec 64)),∀written∈([80,88,104,112,136,168,176,264,272,120,144,216] : List (BitVec 64)),record+offset≠record+written := by
  intro offset member written present
  simp at member present
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>simp
 obtain ⟨frontier,returned,globals,lower,upper,_,domain,endian,code⟩:=frame_new_tail_returned_frame copied post record message codePointer codeLength accessAddresses accessSlots empty frame scratch (record+64) value copiedContext
  (wordAbove 64 (by decide)) (fundingSeparate 64 (by simp)) tailRun
 have preserved (offset : BitVec 64) (member : offset∈([64,72,184,192,208,224] : List (BitVec 64))) : post.memory (record+offset)=copied.memory (record+offset) := by
  have small : offset.toNat<280:=by simp at member;rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>decide
  obtain ⟨_,_,_,_,_,memory,_,_,_⟩:=frame_new_tail_returned_frame copied post record message codePointer codeLength accessAddresses accessSlots empty frame scratch (record+offset) value copiedContext
   (wordAbove offset small) (fundingSeparate offset member) tailRun
  exact memory
 have gasKept:=preserved 64 (by simp)
 have stateKept:=preserved 72 (by simp)
 have usedKept:=preserved 184 (by simp)
 have spillKept:=preserved 192 (by simp)
 have scratchKept:=preserved 208 (by simp)
 have frameKept:=preserved 224 (by simp)
 have initialized:=frame_new_copies_funding s record codePointer codeLength gas stateGas zeroUsed zeroSpill
 refine ⟨frontier,returned,globals,lower,upper,?_,?_,?_,?_,?_,domain,endian,code⟩
 · exact ⟨gasKept.trans initialized.1.1,usedKept.trans initialized.1.2.1,spillKept.trans initialized.1.2.2⟩
 · exact stateKept.trans initialized.2
 · change post.memory (record+208#64)=.word scratchMark
   change s.memory (record+208#64)=.word scratchMark at savedScratch
   simpa [copied,frameNewCopiesPost,sourceWriteWord] using scratchKept.trans (by simpa [copied,frameNewCopiesPost,sourceWriteWord] using savedScratch)
 · change post.memory (record+224#64)=.word frameMark
   change s.memory (record+224#64)=.word frameMark at savedFrame
   simpa [copied,frameNewCopiesPost,sourceWriteWord] using frameKept.trans (by simpa [copied,frameNewCopiesPost,sourceWriteWord] using savedFrame)
 · intro watched beyond
   have separate (offset : BitVec 64) (small : offset.toNat<280) : watched≠record+offset := by
    intro equal
    have bounded : record.toNat+offset.toNat<2^64:=by have:=valid.recordBound;omega
    have eqNat:=congrArg BitVec.toNat equal
    rw [BitVec.toNat_add_of_lt bounded] at eqNat
    omega
   obtain ⟨_,_,_,_,_,memory,_,_,_⟩:=frame_new_tail_returned_frame copied post record message codePointer codeLength accessAddresses accessSlots empty frame scratch watched value copiedContext (by omega)
    (by intro offset member;apply separate offset;simp at member;rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>decide) tailRun
   have n48:=separate 48 (by decide)
   have n56:=separate 56 (by decide)
   have n64:=separate 64 (by decide)
   have n72:=separate 72 (by decide)
   change watched≠record+48#64 at n48
   change watched≠record+56#64 at n56
   change watched≠record+64#64 at n64
   change watched≠record+72#64 at n72
   simpa [copied,frameNewCopiesPost,sourceWriteWord,n48,n56,n64,n72] using memory
#print axioms FrameNewTailContext.after_copies
#print axioms frame_new_copies_tail_returned_funding
end InitECandidate.Runtime
