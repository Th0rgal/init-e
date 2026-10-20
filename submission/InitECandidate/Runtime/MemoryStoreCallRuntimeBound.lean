import InitECandidate.Runtime.MemoryStoreBodyRuntimeBound
import InitECandidate.Runtime.MemoryStoreCallPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual installed dispatch calls to either store have the derived body bound
plus their single call clock, including every failing execution. -/
theorem memory_store_call_bounded
 (kind : MemoryStorePhysicalKind) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (destination : Option (VarKind×MlS))
 (code : s.code=originalRuntimeCode) (budget : memoryStoreBodySourceCost+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (memoryStorePhysicalName kind) []) (memoryStoreBodySourceCost+1) := by
 have installed : s.code.lookup (memoryStorePhysicalName kind)=some ([],memoryStorePhysicalBody kind,.one) := by rw [code];exact memory_store_physical_original_lookup kind
 have lookup:=pan_no_args_shape_lookup s.code.lookup (memoryStorePhysicalName kind) (memoryStorePhysicalBody kind) .one installed
 apply RunBounded.call (bodyCost:=memoryStoreBodySourceCost) rfl budget
 intro body callee returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 exact memory_store_body_bounded kind (callEntryStateHOLFinite s HolFiniteMapExact.empty) upper current ancestors (layout.after_memory rfl rfl) words (valid.after_context rfl rfl rfl) code (by change memoryStoreBodySourceCost≤s.clock-1;omega)
#print axioms memory_store_call_bounded
end InitECandidate.Runtime
