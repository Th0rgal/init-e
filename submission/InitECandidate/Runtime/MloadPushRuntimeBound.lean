import InitECandidate.Runtime.StackPushNoGrowthRuntimeBound
import InitECandidate.Runtime.EvmMloadSource
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem mload_pc_return_bounded : ProgBounded (mloadAt 5) 1 := by
 unfold mloadAt
 apply ProgBounded.weaken
 · vm_bound [vmBound_pc_add]
 · decide
/-- Actual MLOAD push and PC suffix uses the real no-growth operand guard. -/
theorem mload_push_tail_bounded {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 2≤s.clock) :
 RunBounded s (mloadAt 4) 2 := by
 rw [source_mload_4]
 apply RunBounded.seq (a:=1) (b:=1)
 · exact stack_push_no_growth_call_bounded s frame words valid none [.var .local (ofString "v")] inside code (by omega)
 · exact budget
 · intro next normal metadata remaining
   exact RunBounded.ofProg mload_pc_return_bounded (metadata.trans code) remaining
#print axioms mload_push_tail_bounded
end InitECandidate.Runtime
