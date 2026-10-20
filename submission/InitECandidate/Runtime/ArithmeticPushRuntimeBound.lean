import InitECandidate.Runtime.ArithmeticOpcodeSource
import InitECandidate.Runtime.StackPushNoGrowthRuntimeBound
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem arithmetic_pc_return_bounded (kind : ArithmeticOpcodeKind) : ProgBounded (arithmeticOpcodeAt kind 5) 1 := by
 rw [source_arithmetic_opcode_5 kind,source_arithmetic_opcode_6 kind]
 apply ProgBounded.weaken
 · vm_bound [vmBound_pc_add]
 · decide
/-- The actual common push/PC suffix in this original finite arithmetic family
uses its actual no-growth operand guard, including malformed value failures. -/
theorem arithmetic_push_tail_bounded {F : Type}
 (kind : ArithmeticOpcodeKind) (s : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 2≤s.clock) :
 RunBounded s (arithmeticOpcodeAt kind 4) 2 := by
 rw [source_arithmetic_opcode_4 kind]
 apply RunBounded.seq (a:=1) (b:=1)
 · exact stack_push_no_growth_call_bounded s frame words valid none [.var .local (ofString "r")] inside code (by omega)
 · exact budget
 · intro next normal metadata remaining
   exact RunBounded.ofProg (arithmetic_pc_return_bounded kind) (metadata.trans code) remaining
#print axioms arithmetic_push_tail_bounded
end InitECandidate.Runtime
