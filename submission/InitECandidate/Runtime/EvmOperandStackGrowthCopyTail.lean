import InitECandidate.Runtime.EvmOperandStackGrowthSource
import InitECandidate.Runtime.MemcpyNormalFrameAnyClock
import InitECandidate.Runtime.MemcpyNormalStateMetadata
import InitECandidate.Runtime.EncodeHeaderNormalPlan
import InitECandidate.Runtime.FundingAssignReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Actual stack growth copies only into the real fresh scratch allocation,
then updates exactly the stack pointer/capacity header words. -/
theorem stack_push_growth_copy_tail_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame oldBase newBase index capacity scratch watched : BitVec 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atNewBase : s.locals.lookup (ofString "ns")=some (.val (.word newBase)))
 (atIndex : s.locals.lookup (ofString "sp")=some (.val (.word index)))
 (atCapacity : s.locals.lookup (ofString "ncap")=some (.val (.word capacity)))
 (baseDomain : s.memaddrs (frame+8)) (baseAt : s.memory (frame+8)=.word oldBase)
 (indexBound : index.toNat≤capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (allocationExtent : newBase.toNat+capacity.toNat*32≤scratch.toNat)
 (scratchCap : scratch.toNat≤33806089496) (above : scratch.toNat≤watched.toNat)
 (differentBase : watched≠frame+8) (differentCapacity : watched≠frame+232)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (stackPushGrowthAt 4)=(none,post)) :
 post.memory (frame+8)=.word newBase ∧post.memory (frame+232)=.word capacity ∧
 post.memory watched=s.memory watched ∧post.locals=s.locals ∧post.globals=s.globals ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 classical
 have metadata:=evaluateHOLFiniteState_metadata s (stackPushGrowthAt 4)
 rw [run] at metadata
 rw [source_stack_push_growth_4] at run
 obtain ⟨copied,copyRun,storesRun⟩:=encode_header_seq_normal s post _ _ run
 have loaded:=eval_fundingLoad s frame (8#64) oldBase atCurrent baseDomain baseAt
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.load .one (fundingAddress (8#64)))=some (.val (.word oldBase)) at loaded
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "ns"),.load .one (fundingAddress 8),.panop .mul [.var .local (ofString "sp"),.const 32]]=
  some [.val (.word newBase),.val (.word oldBase),.val (.word (index*32))] := by
  change @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "ns"),.load .one (fundingAddress (8#64)),.panop .mul [.var .local (ofString "sp"),.const (32#64)]]=_
  rw [evalListHOLFinite,evalListHOLExact]
  have newEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "ns"))=some (.val (.word newBase)) := by simpa [evalHOLExact] using atNewBase
  rw [newEval,evalListHOLExact,loaded]
  simp [evalListHOLExact,evalHOLExact,atIndex,panOpHOL,valueIsWord,valueWord]
 have sizeNat : (index*32#64).toNat=index.toNat*32 := by rw [BitVec.toNat_mul_of_lt (by change index.toNat*32<2^64;omega)];rfl
 have separateWord : ∀offset : Nat,offset<(index*32#64).toNat → watched≠newBase+BitVec.ofNat 64 offset := by
  intro offset inside equal
  rw [sizeNat] at inside
  have small : offset<2^64:=by omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat=offset:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have nowrap : newBase.toNat+(BitVec.ofNat 64 offset).toNat<2^64:=by rw [offsetNat];omega
  have natural:=congrArg BitVec.toNat equal
  rw [BitVec.toNat_add_of_lt nowrap,offsetNat] at natural
  omega
 have separateByte : ∀offset : Nat,offset<(index*32#64).toNat → watched≠panByteAlignHOL (newBase+BitVec.ofNat 64 offset) := by
  intro offset inside equal
  rw [sizeNat] at inside
  have small : offset<2^64:=by omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat=offset:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have nowrap : newBase.toNat+(BitVec.ofNat 64 offset).toNat<2^64:=by rw [offsetNat];omega
  have natural:=congrArg BitVec.toNat equal
  rw [byteAlign_toNat,BitVec.toNat_add_of_lt nowrap,offsetNat] at natural
  have bounded:=Nat.div_mul_le_self (newBase.toNat+offset) 8
  omega
 have copyFrame:=memcpy_normal_memory_any_clock s copied _ newBase oldBase (index*32#64) watched args code separateWord separateByte (by rw [sizeNat];omega) copyRun
 obtain ⟨locals,globals,_,_,_⟩:=memcpy_normal_state_metadata s copied _ newBase oldBase (index*32#64) args code copyRun
 rw [source_stack_push_growth_5] at storesRun
 obtain ⟨one,firstRun,secondRun⟩:=encode_header_seq_normal copied post _ _ storesRun
 have copiedCurrent : copied.globals.lookup (ofString "ev")=some (.val (.word frame)):=by rw [globals];exact atCurrent
 have firstEq:=store_normal_exact copied one (fundingAddress 8) (.var .local (ofString "ns")) (frame+8) newBase
  (eval_fundingAddress copied frame 8 copiedCurrent) (by change copied.locals.lookup _=_;rw [locals];exact atNewBase) firstRun
 subst one
 have secondEq:=store_normal_exact (sourceWriteWord copied (frame+8) newBase) post (fundingAddress 232) (.var .local (ofString "ncap")) (frame+232) capacity
  (eval_fundingAddress _ frame 232 copiedCurrent) (by change copied.locals.lookup _=_;rw [locals];exact atCapacity) secondRun
 refine ⟨?_,?_,?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [secondEq];simp [sourceWriteWord]
 · rw [secondEq];simp [sourceWriteWord]
 · rw [secondEq]
   change watched≠frame+8#64 at differentBase
   change watched≠frame+232#64 at differentCapacity
   simpa [sourceWriteWord,differentBase,differentCapacity] using copyFrame
 · rw [secondEq];exact locals
 · rw [secondEq];exact globals
#print axioms stack_push_growth_copy_tail_normal
end InitECandidate.Runtime
