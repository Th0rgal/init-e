import InitECandidate.Runtime.StackPopPhysicalRuntimeBound
import InitECandidate.Runtime.MemoryStoreSuffixRuntimeBound
import InitECandidate.Runtime.ChargeWithMemoryCallRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
def memoryStoreBodySourceCost : Nat:=1+(1+((chargeWithMemoryBodyCost+1)+23))
/-- Both actual store bodies have a fixed quantitative all-outcome runtime
bound from concrete initial physical operand/vector state and live funding. -/
theorem memory_store_body_bounded
 (kind : MemoryStorePhysicalKind) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (code : s.code=originalRuntimeCode) (budget : memoryStoreBodySourceCost≤s.clock) :
 RunBounded s (memoryStorePhysicalBody kind) memoryStoreBodySourceCost := by
 change RunBounded s (memoryStorePhysicalBody kind) (1+(1+((chargeWithMemoryBodyCost+1)+23)))
 rw [source_memory_store_physical_body kind,source_memory_store_physical_0 kind]
 apply runBounded_stack_pop_physical_declaration s upper current ancestors layout words valid _ _ _ code (by unfold memoryStoreBodySourceCost at budget;omega)
 intro sa sb sc sd first startAt startKept positive firstValid firstLayout firstCode firstBudget
 rw [source_memory_store_physical_1 kind]
 apply runBounded_stack_pop_physical_declaration first upper current ancestors firstLayout _ firstValid _ _ _ firstCode firstBudget
 intro a b c d second valueAt valueKept secondPositive secondValid secondLayout secondCode secondBudget
 have actualStart : second.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd) := by rw [valueKept (ofString "start") (by decide)];exact startAt
 rw [source_memory_store_physical_2 kind]
 apply RunBounded.seq (a:=chargeWithMemoryBodyCost+1) (b:=23) (state:=second)
 · apply charge_with_memory_discard_call_bounded second upper current ancestors secondLayout _ (fundingU256 sa sb sc sd) (fundingU256 (memoryStorePhysicalWidth kind) 0 0 0) words.memoryBase words.memoryLength words.memoryCapacity words.framePointer words.scratchPointer 3
   · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,actualStart,fundingU256]
   · simp [fundingU256,shapeOfHOLExact]
   · simp [fundingU256,shapeOfHOLExact]
   · exact secondValid.ev
   · intro offset member;exact secondValid.headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;rcases member with rfl|rfl|rfl <;>simp)
   · exact secondValid.memoryBase
   · exact secondValid.memoryLength
   · exact secondValid.memoryCapacity
   · exact secondValid.framePointer
   · exact secondValid.scratchPointer
   · exact secondValid.memoryLengthBound
   · exact secondValid.memoryExtent
   · exact secondValid.pointers
   · exact secondValid.scratch_before_frame
   · exact secondValid.frameExtent
   · exact secondCode
   · omega
 · exact secondBudget
 · intro next normal keptCode nextBudget
   exact RunBounded.ofProg (memory_store_suffix_bounded kind) (keptCode.trans secondCode) nextBudget
#print axioms memory_store_body_bounded
end InitECandidate.Runtime
