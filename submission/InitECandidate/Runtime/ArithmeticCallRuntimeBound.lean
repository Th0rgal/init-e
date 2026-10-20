import InitECandidate.Runtime.ArithmeticBodyRuntimeBound
import InitECandidate.Runtime.OriginalArithmeticAddCode
import InitECandidate.Runtime.OriginalArithmeticSubCode
import InitECandidate.Runtime.OriginalArithmeticMulCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def arithmeticOpcodeName : ArithmeticOpcodeKind→MlS
 | .add=>ofString "op_add"
 | .sub=>ofString "op_sub"
 | .mul=>ofString "op_mul"
theorem arithmetic_opcode_original_lookup (kind : ArithmeticOpcodeKind) : originalRuntimeCode.lookup (arithmeticOpcodeName kind)=some ([],arithmeticOpcodeBody kind,.one) := by
 cases kind with
 | add=>exact originalRuntimeCode_opAdd_lookup
 | sub=>exact originalRuntimeCode_opSub_lookup
 | mul=>exact originalRuntimeCode_opMul_lookup
/-- Actual installed finite arithmetic family dispatch call, all outcomes. -/
theorem arithmetic_opcode_call_bounded
 (kind : ArithmeticOpcodeKind) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (destination : Option (VarKind×MlS))
 (code : s.code=originalRuntimeCode) (budget : arithmeticOpcodeSourceCost kind+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (arithmeticOpcodeName kind) []) (arithmeticOpcodeSourceCost kind+1) := by
 have installed : s.code.lookup (arithmeticOpcodeName kind)=some ([],arithmeticOpcodeBody kind,.one) := by rw [code];exact arithmetic_opcode_original_lookup kind
 have lookup:=pan_no_args_shape_lookup s.code.lookup (arithmeticOpcodeName kind) (arithmeticOpcodeBody kind) .one installed
 apply RunBounded.call (bodyCost:=arithmeticOpcodeSourceCost kind) rfl budget
 intro body callee returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 exact arithmetic_opcode_body_bounded kind (callEntryStateHOLFinite s HolFiniteMapExact.empty) upper current ancestors (layout.after_memory rfl rfl) words (valid.after_context rfl rfl rfl) code (by change arithmeticOpcodeSourceCost kind≤s.clock-1;omega)
#print axioms arithmetic_opcode_original_lookup
#print axioms arithmetic_opcode_call_bounded
end InitECandidate.Runtime
