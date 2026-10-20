import InitECandidate.Runtime.MloadSaturatedPhysicalContext
import InitECandidate.Runtime.ChargeWithMemoryPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem funding_after_record_controls {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (valid : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (domain : post.memaddrs=s.memaddrs)
 (memory : ∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→post.memory watched=s.memory watched) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 have currentAt:=valid.records current (by simp)
 have counterNatural:=interpreter_funding_offset_natural current upper currentAt.extent valid.upperBound (16#64) (by decide)
 constructor
 · exact valid.upperBound
 · intro record member
   have old:=valid.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=post) old domain
   intro offset included
   have offsetBounds : 64≤offset.toNat ∧offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural record upper old.extent valid.upperBound offset offsetBounds.2
   apply memory (record.address+offset) (by rw [natural];have bound:=old.lowerBound;omega)
   · intro equal
     have same:=congrArg BitVec.toNat equal
     change (record.address+offset).toNat=(current.address+0#64).toNat at same
     rw [BitVec.add_zero,natural] at same
     have bound:=old.lowerBound
     omega
   · intro equal
     have same:=congrArg BitVec.toNat equal
     change (record.address+offset).toNat=(current.address+16#64).toNat at same
     rw [natural,counterNatural] at same
     change record.address.toNat+offset.toNat=current.address.toNat+16 at same
     have bound:=old.lowerBound
     omega
 · exact valid.disjoint
 · exact valid.budget
/-- Actual MLOAD charge/read/push/PC suffix retains the whole concrete physical
state and strictly advances actual globally funded used gas. -/
theorem mload_charged_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (sa sb sc sd : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mloadAt 1)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃expansion total newCapacity nextPointer : BitVec 64,
 3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=words.stackSize+1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 let arguments : List (ExpHOL 64):=[.const 3,.var .local (ofString "start"),.rstruct [.const 32,.const 0,.const 0,.const 0]]
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word 3),fundingU256 sa sb sc sd,fundingU256 32 0 0 0] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt,fundingU256]
 rw [source_mload_1] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_with_memory") arguments v) run
 obtain ⟨locals,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,physical,access,chargeFrame⟩:=charge_with_memory_discard_physical_context s next upper current ancestors layout words valid arguments 3 sa sb sc sd 32 0 0 0 args (by decide) code charged
 let nextWords : EvmMemoryOperandWords:={words with memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer}
 change EvmMemoryOperandAt next current.address nextWords at physical
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "charge_with_memory") arguments)
 rw [charged] at metadata
 obtain ⟨zero,finalPhysical,globals,domain,endian,installed,tailFrame⟩:=mload_saturated_returned_physical_context next post current.address nextWords physical sa sb sc sd value (by rw [locals];exact startAt) inside (by intro address below;rw [metadata.2.1];exact fullDomain address below) (metadata.1.trans code) tail
 have finalFunding:=funding_after_record_controls next post upper (current.charged total) ancestors paid domain tailFrame
 refine ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,finalFunding,progress,finalPhysical,domain.trans metadata.2.1,endian.trans metadata.2.2.1,installed.trans metadata.1,?_⟩
 intro watched above notPc notCounter notLength notCapacity notLeft notUsed
 rw [tailFrame watched above notPc notCounter]
 exact chargeFrame watched (by have bound:=valid.scratch_before_frame;omega) notLength notCapacity notLeft notUsed
#print axioms mload_charged_returned_physical_context
end InitECandidate.Runtime
