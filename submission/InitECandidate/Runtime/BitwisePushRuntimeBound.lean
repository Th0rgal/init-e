import InitECandidate.Runtime.BitwiseOpcodeSource
import InitECandidate.Runtime.StackPushNoGrowthRuntimeBound
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem bitwise_pc_return_bounded (kind : BitwiseBinaryKind) : ProgBounded (bitwiseOpcodeAt kind 4) 2 := by
 rw [source_bitwise_opcode_4 kind,source_bitwise_opcode_5 kind]
 apply ProgBounded.weaken
 · vm_bound [vmBound_pc_add]
 · decide
/-- The actual common push/PC suffix of the direct bitwise family evaluates the
real four-limb struct argument, so malformed argument/failure paths end too. -/
theorem bitwise_push_tail_bounded {F : Type}
 (kind : BitwiseBinaryKind) (s : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 1+2≤s.clock) :
 RunBounded s (bitwiseOpcodeAt kind 3) (1+2) := by
 obtain pushStep:=source_bitwise_opcode_3 kind
 rw [pushStep]
 apply RunBounded.seq (a:=1) (b:=2)
 · exact stack_push_no_growth_call_bounded s frame words valid none [bitwisePushValue kind] inside code (by omega)
 · exact budget
 · intro next normal metadata remaining
   exact RunBounded.ofProg (bitwise_pc_return_bounded kind) (metadata.trans code) remaining
#print axioms bitwise_push_tail_bounded
end InitECandidate.Runtime
