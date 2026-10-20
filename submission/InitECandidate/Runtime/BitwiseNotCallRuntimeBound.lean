import InitECandidate.Runtime.BitwiseNotBodyRuntimeBound
import InitECandidate.Runtime.OriginalBitwiseNotCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem not_opcode_original_lookup : originalRuntimeCode.lookup notOpcodeName=some ([],notOpcodeBody,.one) := originalRuntimeCode_opNot_lookup
theorem not_opcode_call_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (destination : Option (VarKind×MlS))
 (code : s.code=originalRuntimeCode) (budget : notOpcodeSourceCost+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) notOpcodeName []) (notOpcodeSourceCost+1) := by
 have installed : s.code.lookup notOpcodeName=some ([],notOpcodeBody,.one) := by rw [code];exact not_opcode_original_lookup
 have lookup:=pan_no_args_shape_lookup s.code.lookup notOpcodeName notOpcodeBody .one installed
 apply RunBounded.call (bodyCost:=notOpcodeSourceCost) rfl budget
 intro body callee returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 exact not_opcode_body_bounded (callEntryStateHOLFinite s HolFiniteMapExact.empty) upper current ancestors (layout.after_memory rfl rfl) words (valid.after_context rfl rfl rfl) code (by change notOpcodeSourceCost≤s.clock-1;omega)
#print axioms not_opcode_original_lookup
#print axioms not_opcode_call_bounded
end InitECandidate.Runtime
