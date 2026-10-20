import InitECandidate.Runtime.EvmMloadSource
import InitECandidate.Runtime.StackPushDiscardFunding
import InitECandidate.Runtime.EvmMstore8PcTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual MLOAD stack_push, pc_add and return retain all live funding. -/
theorem mload_push_tail_returned_funding {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base index capacity scratch frontier pc a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (pcDomain : s.memaddrs (current.address+0)) (pcAt : s.memory (current.address+0)=.word pc)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base) (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrontier : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frontier)))
 (ordered : frontier≤scratch) (scratchBeforeFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 4)=(some (.returned value),post)) :
 value=.val (.word 0) ∧InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 rw [source_mload_4] at run
 obtain ⟨next,pushed,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "stack_push") [.var .local (ofString "v")] v) run
 obtain ⟨funding,pcKept,locals,domain,endian,installed,nextScratch,scratchKept,scratchBound,frontierKept,evKept⟩:=stack_push_discard_normal_funding s next upper current ancestors layout [.var .local (ofString "v")] base index capacity scratch frontier a b c d (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atValue]) atCurrent headerDomain baseAt indexAt capacityAt positive capacityBound indexBound bufferExtent atScratch atFrontier ordered scratchBeforeFrame frameExtent fullDomain code pushed
 have identical : mloadAt 5=mstore8At 5:=rfl
 rw [identical] at tail
 obtain ⟨zero,finalFunding,_⟩:=mstore8_pc_tail_returned_funding next post upper current ancestors funding pc value evKept (by rw [domain];exact pcDomain) (pcKept.trans pcAt) (installed.trans code) tail
 exact ⟨zero,finalFunding⟩
#print axioms mload_push_tail_returned_funding
end InitECandidate.Runtime
