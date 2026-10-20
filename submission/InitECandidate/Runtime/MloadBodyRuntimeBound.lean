import InitECandidate.Runtime.StackPopPhysicalRuntimeBound
import InitECandidate.Runtime.MloadSaturatedRuntimeBound
import InitECandidate.Runtime.ChargeWithMemoryCallRuntimeBound
import InitECandidate.Runtime.ChargeWithMemoryPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
def mloadBodySourceCost : Nat:=1+((chargeWithMemoryBodyCost+1)+36)
/-- Complete original MLOAD runtime includes failed accesses and failed memory
allocation. Real preceding pop ensures the actual final push cannot grow. -/
theorem mload_body_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (code : s.code=originalRuntimeCode) (budget : mloadBodySourceCost≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_op_mload) mloadBodySourceCost := by
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (mloadAt 0) (1+((chargeWithMemoryBodyCost+1)+36))
 rw [source_mload_0]
 apply runBounded_stack_pop_physical_declaration s upper current ancestors layout words valid _ _ _ code budget
 intro a b c d first startAt locals positive physical paid installed remaining
 have inside : (words.stackSize-1#64).toNat<words.stackCapacity.toNat := by
  have decrement : (words.stackSize-1#64).toNat=words.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤words.stackSize.toNat;change 1≤words.stackSize.toNat;omega))
  rw [decrement]
  have bound:=valid.stackSizeBound
  omega
 let arguments : List (ExpHOL 64):=[.const 3,.var .local (ofString "start"),.rstruct [.const 32,.const 0,.const 0,.const 0]]
 have args : evalListHOLFinite first (h:=fun x=>Classical.propDecidable (first.memaddrs x)) arguments=some [.val (.word 3),fundingU256 a b c d,fundingU256 32 0 0 0] := by simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,startAt,fundingU256]
 rw [source_mload_1]
 apply RunBounded.seq (a:=chargeWithMemoryBodyCost+1) (b:=36)
 · apply charge_with_memory_discard_call_bounded first upper current ancestors paid arguments (fundingU256 a b c d) (fundingU256 32 0 0 0) words.memoryBase words.memoryLength words.memoryCapacity words.framePointer words.scratchPointer 3 args
   · simp [fundingU256,shapeOfHOLExact]
   · simp [fundingU256,shapeOfHOLExact]
   · exact physical.ev
   · intro offset member;exact physical.headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;rcases member with rfl|rfl|rfl <;>simp)
   · exact physical.memoryBase
   · exact physical.memoryLength
   · exact physical.memoryCapacity
   · exact physical.framePointer
   · exact physical.scratchPointer
   · exact physical.memoryLengthBound
   · exact physical.memoryExtent
   · exact physical.pointers
   · exact physical.scratch_before_frame
   · exact physical.frameExtent
   · exact installed
   · omega
 · exact remaining
 · intro next normal sameCode nextBudget
   obtain ⟨keptLocals,expansion,total,newCapacity,nextPointer,baseBound,enough,nextFunding,progress,nextPhysical,access,upperFrame⟩:=charge_with_memory_discard_physical_context first next upper current ancestors paid _ physical arguments 3 a b c d 32 0 0 0 args (by decide) installed normal
   exact mload_saturated_tail_bounded next current.address _ nextPhysical a b c d (by rw [keptLocals];exact startAt) inside (sameCode.trans installed) nextBudget
#print axioms mload_body_bounded
end InitECandidate.Runtime
