import InitECandidate.Runtime.BitwiseNotOpcodeSource
import InitECandidate.Runtime.StackPushNoGrowthRuntimeBound
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem not_pc_return_bounded : ProgBounded (notOpcodeAt 3) 2 := by
 rw [source_not_opcode_3,source_not_opcode_4]
 apply ProgBounded.weaken
 · vm_bound [vmBound_pc_add]
 · decide
theorem not_push_tail_bounded {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 1+2≤s.clock) :
 RunBounded s (notOpcodeAt 2) (1+2) := by
 rw [source_not_opcode_2]
 apply RunBounded.seq (a:=1) (b:=2)
 · exact stack_push_no_growth_call_bounded s frame words valid none [notPushValue] inside code (by omega)
 · exact budget
 · intro next normal metadata remaining
   exact RunBounded.ofProg not_pc_return_bounded (metadata.trans code) remaining
#print axioms not_push_tail_bounded
end InitECandidate.Runtime
