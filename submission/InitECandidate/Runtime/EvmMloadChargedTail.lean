import InitECandidate.Runtime.EvmMloadSaturatedTail
import InitECandidate.Runtime.ChargeWithMemoryDiscardUpperFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem mload_charge_header_offsets_ne (left right : BitVec 64)
 (leftMember : left∈([0,8,16,232] : List (BitVec 64)))
 (rightMember : right∈([32,40,64,184] : List (BitVec 64))) : left≠right := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at leftMember rightMember
 rcases leftMember with rfl|rfl|rfl|rfl <;>rcases rightMember with rfl|rfl|rfl|rfl <;>decide
/-- Actual MLOAD from its literal three-gas charged-memory call through the
real read/push/PC tail has strict actual used-gas progress. -/
theorem mload_charged_tail_returned_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base index capacity scratch pointer pc memoryBase memoryLength memoryCapacity sa sb sc sd : BitVec 64) (value : ValueHOL 64)
 (currentAligned : memoryLength.toNat%32=0)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([0,8,16,24,32,40,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base)
 (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (memoryAt : s.memory (current.address+24)=.word memoryBase)
 (lengthAt : s.memory (current.address+32)=.word memoryLength)
 (memoryCapacityAt : s.memory (current.address+40)=.word memoryCapacity)
 (pcAt : s.memory (current.address+0)=.word pc)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : memoryLength.toNat≤memoryCapacity.toNat)
 (oldExtent : memoryBase.toNat+memoryCapacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat) (belowFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 1)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃total : BitVec 64,3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) := by
 let arguments : List (ExpHOL 64):=[.const 3,.var .local (ofString "start"),.rstruct [.const 32,.const 0,.const 0,.const 0]]
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word 3),fundingU256 sa sb sc sd,fundingU256 32 0 0 0] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt,fundingU256]
 rw [source_mload_1] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_with_memory") arguments v) run
 have domains : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset) := by
  intro offset member;exact headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)
 obtain ⟨locals,expansion,total,small,baseBound,enough,paid,used,progress,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,lengthBound,newAligned,access,extent,mono,within,evKept,scratchKept,pointerKept,domain,endian,installed⟩:=charge_with_memory_discard_access_progress s next upper current ancestors layout arguments memoryBase memoryLength memoryCapacity pointer scratch 3 sa sb sc sd 32 0 0 0 args currentAligned (by decide) atFrame domains memoryAt lengthAt memoryCapacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent code charged
 have keep (offset : BitVec 64) (member : offset∈([0,8,16,232] : List (BitVec 64))) : next.memory (current.address+offset)=s.memory (current.address+offset) := by
  have smallOffset : offset.toNat<280 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member;rcases member with rfl|rfl|rfl|rfl <;>decide
  have natural:=interpreter_funding_offset_natural current 33806089496 frameExtent (by decide) offset smallOffset
  apply charge_with_memory_discard_upper_frame s next upper current ancestors layout arguments (fundingU256 sa sb sc sd) (fundingU256 32 0 0 0) memoryBase memoryLength memoryCapacity pointer scratch 3 (current.address+offset) args (by simp [fundingU256,shapeOfHOLExact]) (by simp [fundingU256,shapeOfHOLExact]) atFrame domains memoryAt lengthAt memoryCapacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent (by rw [natural];omega)
  all_goals first
   | exact code
   | exact charged
   | (intro equal;exact (mload_charge_header_offsets_ne offset _ member (by simp)) (add_left_cancel equal))
 obtain ⟨zero,finalFunding⟩:=mload_saturated_tail_returned_funding next post upper (current.charged total) ancestors paid base index capacity scratch nextPointer pc memoryBase sa sb sc sd value (by rw [locals];exact startAt) (by rw [domain];exact headerDomain 24 (by simp)) baseKept (by rw [domain];exact headerDomain 0 (by simp)) ((keep 0 (by simp)).trans pcAt) evKept (by intro offset member;rw [domain];exact headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)) ((keep 8 (by simp)).trans baseAt) ((keep 16 (by simp)).trans indexAt) ((keep 232 (by simp)).trans capacityAt) positive capacityBound indexBound bufferExtent scratchKept pointerKept (by exact BitVec.le_def.mpr within) belowFrame frameExtent (by intro address below;rw [domain];exact fullDomain address below) (installed.trans code) tail
 exact ⟨zero,total,baseBound,enough,finalFunding,progress⟩
#print axioms mload_charged_tail_returned_progress
end InitECandidate.Runtime
