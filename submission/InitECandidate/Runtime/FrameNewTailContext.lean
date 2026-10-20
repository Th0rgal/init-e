import InitECandidate.Runtime.FrameNewScratchDeclarationReturned
import InitECandidate.Runtime.FrameNewStoreReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure FrameNewTailContext {F : Type} (s : PanSemStateFiniteExact 64 F)
 (record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64) : Prop where
 atRecord : s.locals.lookup (ofString "e")=some (.val (.word record))
 atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message))
 atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch))
 atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame))
 atEmpty : s.globals.lookup (ofString "evm_empty")=some (.val (.word empty))
 ordered : frame.toNat≤scratch.toNat
 scratchBelow : scratch.toNat≤record.toNat
 recordBound : record.toNat+280≤33806089496
 beforeMessage : record.toNat+280≤message.toNat
 messageBound : message.toNat+176≤2^64
 messageDomain : ∀offset∈([112,120,152,160] : List (BitVec 64)),s.memaddrs (message+offset)
 codeAt : s.memory (message+112)=.word codePointer
 lengthAt : s.memory (message+120)=.word codeLength
 addressesAt : s.memory (message+152)=.word accessAddresses
 slotsAt : s.memory (message+160)=.word accessSlots
 lengthBound : codeLength.toNat≤134217712
 sourceCode : s.code=originalRuntimeCode

theorem FrameNewTailContext.message_above_scratch {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (offset : BitVec 64) (small : offset.toNat<176) : scratch.toNat≤(message+offset).toNat := by
 have bounded : message.toNat+offset.toNat<2^64:=by have:=valid.messageBound;omega
 rw [BitVec.toNat_add_of_lt bounded]
 have:=valid.beforeMessage
 have:=valid.scratchBelow
 omega

/-- Transport the concrete caller context across an actual descending
scratch constructor's upper-memory frame. -/
theorem FrameNewTailContext.after_upper_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (post : PanSemStateFiniteExact 64 F) (frontier : BitVec 64)
 (atRecord : post.locals.lookup (ofString "e")=some (.val (.word record)))
 (atMessage : post.locals.lookup (ofString "msg")=some (.val (.word message)))
 (globals : post.globals=s.globals.update (ofString "scratch_ptr",.val (.word frontier)))
 (lower : frame.toNat≤frontier.toNat) (upper : frontier.toNat≤scratch.toNat)
 (domain : post.memaddrs=s.memaddrs) (code : post.code=s.code)
 (memory : ∀watched : BitVec 64,scratch.toNat≤watched.toNat → post.memory watched=s.memory watched) :
 FrameNewTailContext post record message codePointer codeLength accessAddresses accessSlots empty frame frontier := by
 constructor
 · exact atRecord
 · exact atMessage
 · simp [globals,HolFiniteMapExact.lookup_update,FUPDATE]
 · have different : ofString "scratch_ptr"≠ofString "frame_mem_ptr":=by decide
   simpa [globals,HolFiniteMapExact.lookup_update,FUPDATE,different] using valid.atFrame
 · have different : ofString "scratch_ptr"≠ofString "evm_empty":=by decide
   simpa [globals,HolFiniteMapExact.lookup_update,FUPDATE,different] using valid.atEmpty
 · exact lower
 · exact upper.trans valid.scratchBelow
 · exact valid.recordBound
 · exact valid.beforeMessage
 · exact valid.messageBound
 · intro offset member
   rw [domain]
   exact valid.messageDomain offset member
 · rw [memory _ (valid.message_above_scratch 112 (by decide))]
   exact valid.codeAt
 · rw [memory _ (valid.message_above_scratch 120 (by decide))]
   exact valid.lengthAt
 · rw [memory _ (valid.message_above_scratch 152 (by decide))]
   exact valid.addressesAt
 · rw [memory _ (valid.message_above_scratch 160 (by decide))]
   exact valid.slotsAt
 · exact valid.lengthBound
 · exact code.trans valid.sourceCode

/-- A real scalar record write cannot alter any old message input cell. -/
theorem FrameNewTailContext.after_record_write {F : Type} {s : PanSemStateFiniteExact 64 F}
 {record message codePointer codeLength accessAddresses accessSlots empty frame scratch : BitVec 64}
 (valid : FrameNewTailContext s record message codePointer codeLength accessAddresses accessSlots empty frame scratch)
 (offset word : BitVec 64) (small : offset.toNat<280) :
 FrameNewTailContext (sourceWriteWord s (record+offset) word) record message codePointer codeLength accessAddresses accessSlots empty frame scratch := by
 have separate (sourceOffset : BitVec 64) (inside : sourceOffset.toNat<176) : message+sourceOffset≠record+offset :=
  (frame_new_message_cell_separated record message offset sourceOffset valid.beforeMessage valid.messageBound small inside).symm
 refine ⟨valid.atRecord,valid.atMessage,valid.atScratch,valid.atFrame,valid.atEmpty,valid.ordered,valid.scratchBelow,
  valid.recordBound,valid.beforeMessage,valid.messageBound,valid.messageDomain,?_,?_,?_,?_,valid.lengthBound,valid.sourceCode⟩
 · change (if message+112=record+offset then _ else _)=_
   rw [if_neg (separate 112 (by decide))]
   exact valid.codeAt
 · change (if message+120=record+offset then _ else _)=_
   rw [if_neg (separate 120 (by decide))]
   exact valid.lengthAt
 · change (if message+152=record+offset then _ else _)=_
   rw [if_neg (separate 152 (by decide))]
   exact valid.addressesAt
 · change (if message+160=record+offset then _ else _)=_
   rw [if_neg (separate 160 (by decide))]
   exact valid.slotsAt
#print axioms FrameNewTailContext.message_above_scratch
#print axioms FrameNewTailContext.after_upper_frame
#print axioms FrameNewTailContext.after_record_write
end InitECandidate.Runtime
