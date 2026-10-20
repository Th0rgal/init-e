import InitECandidate.Runtime.EvmMstoreSaturatedTail
import InitECandidate.Runtime.ChargeWithMemoryDiscardUpperFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual MSTORE from its literal three-gas memory charge through return has
strict real global gas progress and preserves every live funding record. -/
theorem mstore_charged_tail_returned_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity pointer scratch pc sa sb sc sd a b c d : BitVec 64) (value : ValueHOL 64)
 (currentAligned : length.toNat%32=0)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([0,24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base)
 (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (pcAt : s.memory (current.address+0)=.word pc)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (mstoreAt 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃total : BitVec 64,3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) := by
 let arguments : List (ExpHOL 64):=[.const 3,.var .local (ofString "start"),.rstruct [.const 32,.const 0,.const 0,.const 0]]
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word 3),fundingU256 sa sb sc sd,fundingU256 32 0 0 0] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt,fundingU256]
 rw [source_mstore_2] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_with_memory") arguments v) run
 have domains : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset) := by
  intro offset member;exact headerDomain offset (by simp only [List.mem_cons] at member ⊢;tauto)
 obtain ⟨locals,expansion,total,small,baseBound,enough,paid,used,progress,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,lengthBound,newAligned,access,extent,mono,within,evKept,scratchKept,pointerKept,domain,endian,installed⟩:=charge_with_memory_discard_access_progress s next upper current ancestors layout arguments base length capacity pointer scratch 3 sa sb sc sd 32 0 0 0 args currentAligned (by decide) atFrame domains baseAt lengthAt capacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent code charged
 have byteSpan : base.toNat+(evmSatWord sa sb sc sd).toNat+32≤scratch.toNat := by
  have span:=access (by simp [evmSatWord])
  change (evmSatWord sa sb sc sd).toNat+32≤(length+expansion).toNat at span
  omega
 have pcKept : next.memory (current.address+0)=s.memory (current.address+0) := by
  apply charge_with_memory_discard_upper_frame s next upper current ancestors layout arguments (fundingU256 sa sb sc sd) (fundingU256 32 0 0 0) base length capacity pointer scratch 3 (current.address+0) args (by simp [fundingU256,shapeOfHOLExact]) (by simp [fundingU256,shapeOfHOLExact]) atFrame domains baseAt lengthAt capacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent (by simpa using belowFrame) (by intro equal; have impossible : (0#64)=(32#64):=add_left_cancel equal; exact (by decide : (0#64)≠(32#64)) impossible) (by intro equal; have impossible : (0#64)=(40#64):=add_left_cancel equal; exact (by decide : (0#64)≠(40#64)) impossible) (by intro equal; have impossible : (0#64)=(64#64):=add_left_cancel equal; exact (by decide : (0#64)≠(64#64)) impossible) (by intro equal; have impossible : (0#64)=(184#64):=add_left_cancel equal; exact (by decide : (0#64)≠(184#64)) impossible) code charged
 obtain ⟨zero,finalFunding,_,_,_,_⟩:=mstore_saturated_tail_returned_funding next post upper (current.charged total) ancestors paid base scratch pc sa sb sc sd a b c d value evKept (by intro offset member;rw [domain];exact headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)) baseKept (pcKept.trans pcAt) (by rw [locals];exact startAt) (by rw [locals];exact valueAt) byteSpan belowFrame (installed.trans code) (by rw [domain];exact domOK) tail
 exact ⟨zero,total,baseBound,enough,finalFunding,progress⟩
#print axioms mstore_charged_tail_returned_progress
end InitECandidate.Runtime
