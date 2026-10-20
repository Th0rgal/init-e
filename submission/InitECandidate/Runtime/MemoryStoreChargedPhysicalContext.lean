import InitECandidate.Runtime.MemoryStorePhysicalSource
import InitECandidate.Runtime.Mstore8SaturatedPhysicalContext
import InitECandidate.Runtime.MstoreSaturatedPhysicalContext
import InitECandidate.Runtime.ChargeWithMemoryPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
private theorem funding_after_upper_pc_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (valid : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (scratch : BitVec 64) (below : scratch.toNat≤current.address.toNat)
 (domain : post.memaddrs=s.memaddrs)
 (memory : ∀watched : BitVec 64,scratch.toNat≤watched.toNat→watched≠current.address+0→post.memory watched=s.memory watched) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 constructor
 · exact valid.upperBound
 · intro record member
   have old:=valid.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=post) old domain
   intro offset included
   have offsetBounds : 0<offset.toNat ∧offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural record upper old.extent valid.upperBound offset offsetBounds.2
   apply memory (record.address+offset) (by rw [natural];have bound:=old.lowerBound;omega)
   intro equal
   have same:=congrArg BitVec.toNat equal
   change (record.address+offset).toNat=(current.address+0#64).toNat at same
   simp only [BitVec.add_zero] at same
   rw [natural] at same
   have bound:=old.lowerBound
   omega
 · exact valid.disjoint
 · exact valid.budget
/-- Exactly the real MSTORE8/MSTORE charge and original suffixes close physical
memory/operand state and funded progress. No suffix/callee contract is assumed. -/
theorem memory_store_charged_returned_physical_context
 (kind : MemoryStorePhysicalKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (sa sb sc sd a b c d : BitVec 64) (value : ValueHOL 64)
 (startAt : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (valueAt : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (memoryStorePhysicalAt kind 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃expansion total newCapacity nextPointer : BitVec 64,
 3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 let width:=memoryStorePhysicalWidth kind
 let arguments : List (ExpHOL 64):=[.const 3,.var .local (ofString "start"),.rstruct [.const width,.const 0,.const 0,.const 0]]
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) arguments=some [.val (.word 3),fundingU256 sa sb sc sd,fundingU256 width 0 0 0] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt,fundingU256]
 rw [source_memory_store_physical_2] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_with_memory") arguments v) run
 obtain ⟨locals,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,physical,access,chargeFrame⟩:=charge_with_memory_discard_physical_context s next upper current ancestors layout words valid arguments 3 sa sb sc sd width 0 0 0 args (by decide) code charged
 let nextWords : EvmMemoryOperandWords:={words with memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer}
 change EvmMemoryOperandAt next current.address nextWords at physical
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "charge_with_memory") arguments)
 rw [charged] at metadata
 have widthSat : evmSatWord width 0 0 0=width := by simp [evmSatWord]
 have widthNonzero : width≠0#64 := by cases kind <;>decide
 have span:=access (by rw [widthSat];exact widthNonzero)
 rw [widthSat] at span
 have extent : words.memoryBase.toNat+(evmSatWord sa sb sc sd).toNat+width.toNat≤words.scratchPointer.toNat := by
  have first:=physical.memoryLengthBound
  have second:=physical.memoryExtent
  have third:=physical.pointers
  change (words.memoryLength+expansion).toNat≤newCapacity.toNat at first
  change words.memoryBase.toNat+newCapacity.toNat≤nextPointer.toNat at second
  change nextPointer.toNat≤words.scratchPointer.toNat at third
  omega
 have startKept : next.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd) := by rw [locals];exact startAt
 have valueKept : next.locals.lookup (ofString "value")=some (fundingU256 a b c d) := by rw [locals];exact valueAt
 have suffix : value=.val (.word 0) ∧EvmMemoryOperandAt post current.address {nextWords with pc:=nextWords.pc+1} ∧
  post.globals=next.globals ∧post.memaddrs=next.memaddrs ∧post.be=next.be ∧post.code=next.code ∧
  (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠current.address+0→post.memory watched=next.memory watched) := by
  cases kind with
  | byte=>
   exact mstore8_saturated_returned_physical_context next post current.address nextWords physical sa sb sc sd a b c d value startKept valueKept extent (metadata.1.trans code) tail
  | word=>
   exact mstore_saturated_returned_physical_context next post current.address nextWords physical sa sb sc sd a b c d value startKept valueKept extent (metadata.1.trans code) (by rw [metadata.2.1];exact domOK) tail
 obtain ⟨zero,finalPhysical,globals,domain,endian,installed,tailFrame⟩:=suffix
 have finalFunding:=funding_after_upper_pc_frame next post upper (current.charged total) ancestors paid words.scratchPointer valid.scratch_before_frame domain tailFrame
 refine ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,finalFunding,progress,finalPhysical,domain.trans metadata.2.1,endian.trans metadata.2.2.1,installed.trans metadata.1,?_⟩
 intro watched above notPc notLength notCapacity notLeft notUsed
 rw [tailFrame watched above notPc]
 exact chargeFrame watched above notLength notCapacity notLeft notUsed
#print axioms memory_store_charged_returned_physical_context
end InitECandidate.Runtime
