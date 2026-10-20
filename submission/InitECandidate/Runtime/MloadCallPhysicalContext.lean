import InitECandidate.Runtime.MloadBodyPhysicalContext
import InitECandidate.Runtime.OriginalMloadCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed dispatch-style MLOAD closes its real next-opcode physical
and funded state, including original operand size and restored caller locals. -/
theorem mload_discard_normal_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "op_mload") [])=(none,post)) :
 post.locals=s.locals ∧∃expansion total newCapacity nextPointer : BitVec 64,
 3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 have installed : s.code.lookup (ofString "op_mload")=some ([],sourceFunctionBody Guest.guestFn_op_mload,.one) := by rw [code];exact originalRuntimeCode_opMload_lookup
 have lookup:=pan_no_args_shape_lookup s.code.lookup (ofString "op_mload") (sourceFunctionBody Guest.guestFn_op_mload) .one installed
 obtain ⟨value,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "op_mload") [] [] (sourceFunctionBody Guest.guestFn_op_mload) HolFiniteMapExact.empty .one rfl lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "op_mload") [] [] (sourceFunctionBody Guest.guestFn_op_mload) HolFiniteMapExact.empty .one rfl lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have entryFunding : InterpreterFundingLayout entry current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 have entryPhysical : EvmMemoryOperandAt entry current.address words:=valid.after_context rfl rfl rfl
 obtain ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,physical,domain,endian,installedKept,upperFrame⟩:=mload_body_returned_physical_context entry body upper current ancestors entryFunding words entryPhysical value fullDomain code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "op_mload") [])
 rw [run] at metadata
 have postDomain : post.memaddrs=body.memaddrs:=metadata.2.1.trans domain.symm
 refine ⟨locals,expansion,total,newCapacity,nextPointer,baseBound,enough,paid.after_memory memory postDomain,progress,physical.after_context globals memory postDomain,metadata.2.1,metadata.2.2.1,metadata.1,?_⟩
 intro watched above notPc notCounter notLength notCapacity notLeft notUsed
 rw [memory]
 exact upperFrame watched above notPc notCounter notLength notCapacity notLeft notUsed
#print axioms mload_discard_normal_physical_context
end InitECandidate.Runtime
