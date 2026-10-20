import InitECandidate.Runtime.MloadBodyRuntimeBound
import InitECandidate.Runtime.OriginalMloadCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual installed MLOAD at arbitrary destination, all outcomes. -/
theorem mload_call_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (destination : Option (VarKind×MlS))
 (code : s.code=originalRuntimeCode) (budget : mloadBodySourceCost+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "op_mload") []) (mloadBodySourceCost+1) := by
 have installed : s.code.lookup (ofString "op_mload")=some ([],sourceFunctionBody Guest.guestFn_op_mload,.one) := by rw [code];exact originalRuntimeCode_opMload_lookup
 have lookup:=pan_no_args_shape_lookup s.code.lookup (ofString "op_mload") (sourceFunctionBody Guest.guestFn_op_mload) .one installed
 apply RunBounded.call (bodyCost:=mloadBodySourceCost) rfl budget
 intro body callee returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 exact mload_body_bounded (callEntryStateHOLFinite s HolFiniteMapExact.empty) upper current ancestors (layout.after_memory rfl rfl) words (valid.after_context rfl rfl rfl) code (by change mloadBodySourceCost≤s.clock-1;omega)
#print axioms mload_call_bounded
end InitECandidate.Runtime
