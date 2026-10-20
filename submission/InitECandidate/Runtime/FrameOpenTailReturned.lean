import InitECandidate.Runtime.FrameOpenFinalStores
import InitECandidate.Runtime.FrameOpenZeroPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Actual104-byte continuation construction after frame_new, including all
link fields, done=0, current-frame globals and protected older-frame memory. -/
theorem frame_open_tail_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame parent previous kind message child : BitVec 64) (value : ValueHOL 64)
 (atParent : s.locals.lookup (ofString "parent")=some (.val (.word parent)))
 (atPrevious : s.globals.lookup (ofString "cur_cont")=some (.val (.word previous)))
 (atKind : s.locals.lookup (ofString "kind")=some (.val (.word kind)))
 (atMessage : s.locals.lookup (ofString "msg")=some (.val (.word message)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (domain : ∀offset : Nat,offset<104 → s.memaddrs (panByteAlignHOL (scratchAllocationEnd scratch 104+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s (frameOpenAt 2)=(some (.returned value),post)) :
 let record:=scratchAllocationEnd scratch 104
 value=.val (.word child) ∧
 post.globals=((s.globals.update (ofString "scratch_ptr",.val (.word record))).update (ofString "ev",.val (.word child))).update (ofString "cur_cont",.val (.word record)) ∧
 frame.toNat≤record.toNat ∧record.toNat+104≤scratch.toNat ∧record.toNat%8=0 ∧
 post.memory record=.word parent ∧post.memory (record+8)=.word previous ∧post.memory (record+16)=.word kind ∧
 post.memory (record+32)=.word 0 ∧post.memory (record+40)=.word message ∧
 (∀watched : BitVec 64,scratch.toNat≤watched.toNat → post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (frameOpenAt 2)
 rw [run] at metadata
 obtain ⟨zeroed,output,zeroRun,zeroContext,memory,globals,_,_,_⟩:=frame_open_zero_prefix_returned s post scratch frame value atScratch atFrame (BitVec.le_def.mpr ordered) cap code domain run
 let record:=scratchAllocationEnd scratch 104
 have parentKept : zeroed.locals.lookup (ofString "parent")=some (.val (.word parent)) := by rw [zeroContext.otherLocals _ (by decide)];exact atParent
 have previousKept : zeroed.globals.lookup (ofString "cur_cont")=some (.val (.word previous)) := by simpa (config:={decide:=true}) [zeroContext.globals,HolFiniteMapExact.lookup_update,FUPDATE] using atPrevious
 have kindKept : zeroed.locals.lookup (ofString "kind")=some (.val (.word kind)) := by rw [zeroContext.otherLocals _ (by decide)];exact atKind
 have messageKept : zeroed.locals.lookup (ofString "msg")=some (.val (.word message)) := by rw [zeroContext.otherLocals _ (by decide)];exact atMessage
 have childKept : zeroed.locals.lookup (ofString "child")=some (.val (.word child)) := by rw [zeroContext.otherLocals _ (by decide)];exact atChild
 obtain ⟨returned,outputEq⟩:=frame_open_final_stores_returned zeroed output record parent previous kind message child value zeroContext.atRecord parentKept previousKept kindKept messageKept childKept zeroRun
 have endpointMemory : post.memory=(frameOpenFinalPost zeroed record parent previous kind message child).memory:=by rw [memory,outputEq];rfl
 have endpointGlobals : post.globals=(frameOpenFinalPost zeroed record parent previous kind message child).globals:=by rw [globals,outputEq];rfl
 refine ⟨returned,?_,zeroContext.lower,zeroContext.extent,scratchAllocationEnd_mask_aligned scratch 104,?_,?_,?_,?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [endpointGlobals]
   change ((zeroed.globals.update (ofString "ev",.val (.word child))).update (ofString "cur_cont",.val (.word record)))=_
   rw [zeroContext.globals]
 · rw [endpointMemory]
   simp [frameOpenFinalPost,setKvarHOLFinite,setGlobalHOLFinite,sourceWriteWord,record]
 · rw [endpointMemory]
   simp [frameOpenFinalPost,setKvarHOLFinite,setGlobalHOLFinite,sourceWriteWord,record]
 · rw [endpointMemory]
   simp [frameOpenFinalPost,setKvarHOLFinite,setGlobalHOLFinite,sourceWriteWord,record]
 · rw [endpointMemory]
   simpa [frameOpenFinalPost,setKvarHOLFinite,setGlobalHOLFinite,sourceWriteWord,record] using zeroContext.zeroWords 32 (by decide) (by decide)
 · rw [endpointMemory]
   simp [frameOpenFinalPost,setKvarHOLFinite,setGlobalHOLFinite,sourceWriteWord,record]
 · intro watched beyond
   rw [endpointMemory,frame_open_final_stores_word_frame zeroed record parent previous kind message child watched]
   · exact zeroContext.upperMemory watched beyond
   · intro offset member equal
     have small : offset.toNat<104:=by simp at member;rcases member with rfl|rfl|rfl|rfl <;>decide
     have extent:=zeroContext.extent
     change record.toNat+104≤scratch.toNat at extent
     have bounded : record.toNat+offset.toNat<2^64:=by omega
     have natural:=congrArg BitVec.toNat equal
     rw [BitVec.toNat_add_of_lt bounded] at natural
     omega
#print axioms frame_open_tail_returned
end InitECandidate.Runtime
