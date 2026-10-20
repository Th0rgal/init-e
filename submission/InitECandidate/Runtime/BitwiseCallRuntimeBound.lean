import InitECandidate.Runtime.BitwiseBodyRuntimeBound
import InitECandidate.Runtime.OriginalBitwiseAndCode
import InitECandidate.Runtime.OriginalBitwiseOrCode
import InitECandidate.Runtime.OriginalBitwiseXorCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem bitwise_opcode_original_lookup (kind : BitwiseBinaryKind) : originalRuntimeCode.lookup (bitwiseOpcodeName kind)=some ([],bitwiseOpcodeBody kind,.one) := by
 cases kind with
 | and=>exact originalRuntimeCode_opAnd_lookup
 | or=>exact originalRuntimeCode_opOr_lookup
 | xor=>exact originalRuntimeCode_opXor_lookup
/-- Actual installed finite direct bitwise family dispatch call, all outcomes. -/
theorem bitwise_opcode_call_bounded
 (kind : BitwiseBinaryKind) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (destination : Option (VarKind×MlS))
 (code : s.code=originalRuntimeCode) (budget : bitwiseOpcodeSourceCost kind+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (bitwiseOpcodeName kind) []) (bitwiseOpcodeSourceCost kind+1) := by
 have installed : s.code.lookup (bitwiseOpcodeName kind)=some ([],bitwiseOpcodeBody kind,.one) := by rw [code];exact bitwise_opcode_original_lookup kind
 have lookup:=pan_no_args_shape_lookup s.code.lookup (bitwiseOpcodeName kind) (bitwiseOpcodeBody kind) .one installed
 apply RunBounded.call (bodyCost:=bitwiseOpcodeSourceCost kind) rfl budget
 intro body callee returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 exact bitwise_opcode_body_bounded kind (callEntryStateHOLFinite s HolFiniteMapExact.empty) upper current ancestors (layout.after_memory rfl rfl) words (valid.after_context rfl rfl rfl) code (by change bitwiseOpcodeSourceCost kind≤s.clock-1;omega)
#print axioms bitwise_opcode_original_lookup
#print axioms bitwise_opcode_call_bounded
end InitECandidate.Runtime
