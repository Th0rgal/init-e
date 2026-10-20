import InitECandidate.Runtime.BitwiseBodyPhysicalContext
import InitECandidate.Runtime.BitwiseCallRuntimeBound
import InitECandidate.Runtime.PanDiscardNormalBody
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed discard-form bitwise dispatch call closes the concrete
next physical/funding state of the real op_and/op_or/op_xor entries. -/
theorem bitwise_discard_normal_physical_context
 (kind : BitwiseBinaryKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (bitwiseOpcodeName kind) [])=(none,post)) :
 post.locals=s.locals ∧bitwiseOpcodeFee kind≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged (bitwiseOpcodeFee kind)::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged (bitwiseOpcodeFee kind)::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 have installed : s.code.lookup (bitwiseOpcodeName kind)=some ([],bitwiseOpcodeBody kind,.one) := by
  rw [code];exact bitwise_opcode_original_lookup kind
 have lookup:=pan_no_args_shape_lookup s.code.lookup (bitwiseOpcodeName kind) (bitwiseOpcodeBody kind) .one installed
 obtain ⟨value,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (bitwiseOpcodeName kind) [] [] (bitwiseOpcodeBody kind) HolFiniteMapExact.empty .one rfl lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (bitwiseOpcodeName kind) [] [] (bitwiseOpcodeBody kind) HolFiniteMapExact.empty .one rfl lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have entryFunding : InterpreterFundingLayout entry current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 have entryPhysical : EvmMemoryOperandAt entry current.address words:=valid.after_context rfl rfl rfl
 have entryCode : entry.code=originalRuntimeCode:=code
 obtain ⟨zero,enough,paid,progress,physical,bodyGlobals,domain,endian,installedKept,upperFrame⟩:=bitwise_opcode_body_returned_physical_context kind entry body upper current ancestors entryFunding words entryPhysical value fullDomain entryCode bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (bitwiseOpcodeName kind) [])
 rw [run] at metadata
 have postDomain : post.memaddrs=body.memaddrs:=metadata.2.1.trans domain.symm
 have postGlobals : post.globals=s.globals:=globals.trans bodyGlobals
 refine ⟨locals,enough,paid.after_memory memory postDomain,progress,physical.after_context globals memory postDomain,postGlobals,metadata.2.1,metadata.2.2.1,metadata.1,?_⟩
 intro watched above notPc notCounter notLeft notUsed
 rw [memory]
 exact upperFrame watched above notPc notCounter notLeft notUsed
#print axioms bitwise_discard_normal_physical_context
end InitECandidate.Runtime
