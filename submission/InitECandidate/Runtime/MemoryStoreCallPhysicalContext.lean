import InitECandidate.Runtime.MemoryStoreBodyPhysicalContext
import InitECandidate.Runtime.OriginalMstore8Code
import InitECandidate.Runtime.OriginalMstoreCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def memoryStorePhysicalName : MemoryStorePhysicalKind→MlS
 | .byte=>ofString "op_mstore8"
 | .word=>ofString "op_mstore"

theorem memory_store_physical_original_lookup (kind : MemoryStorePhysicalKind) :
 originalRuntimeCode.lookup (memoryStorePhysicalName kind)=some ([],memoryStorePhysicalBody kind,.one) := by
 cases kind with
 | byte=>exact originalRuntimeCode_opMstore8_lookup
 | word=>exact originalRuntimeCode_opMstore_lookup
/-- Actual installed dispatch-style memory store call closes the concrete
physical/funding state for another real opcode, and restores caller locals. -/
theorem memory_store_discard_normal_physical_context
 (kind : MemoryStorePhysicalKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (memoryStorePhysicalName kind) [])=(none,post)) :
 post.locals=s.locals ∧∃expansion total newCapacity nextPointer : BitVec 64,
 3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 have installed : s.code.lookup (memoryStorePhysicalName kind)=some ([],memoryStorePhysicalBody kind,.one) := by rw [code];exact memory_store_physical_original_lookup kind
 have lookup:=pan_no_args_shape_lookup s.code.lookup (memoryStorePhysicalName kind) (memoryStorePhysicalBody kind) .one installed
 obtain ⟨value,body,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (memoryStorePhysicalName kind) [] [] (memoryStorePhysicalBody kind) HolFiniteMapExact.empty .one rfl lookup run
 obtain ⟨other,otherBody,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (memoryStorePhysicalName kind) [] [] (memoryStorePhysicalBody kind) HolFiniteMapExact.empty .one rfl lookup run
 have equal : otherBody=body:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherBody
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have entryFunding : InterpreterFundingLayout entry current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 have entryPhysical : EvmMemoryOperandAt entry current.address words:=valid.after_context rfl rfl rfl
 obtain ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,physical,domain,endian,installedKept,upperFrame⟩:=memory_store_body_returned_physical_context kind entry body upper current ancestors entryFunding words entryPhysical value code domOK bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (memoryStorePhysicalName kind) [])
 rw [run] at metadata
 have postDomain : post.memaddrs=body.memaddrs:=metadata.2.1.trans domain.symm
 refine ⟨locals,expansion,total,newCapacity,nextPointer,baseBound,enough,paid.after_memory memory postDomain,progress,physical.after_context globals memory postDomain,metadata.2.1,metadata.2.2.1,metadata.1,?_⟩
 intro watched above notPc notCounter notLength notCapacity notLeft notUsed
 rw [memory]
 exact upperFrame watched above notPc notCounter notLength notCapacity notLeft notUsed
#print axioms memory_store_physical_original_lookup
#print axioms memory_store_discard_normal_physical_context
end InitECandidate.Runtime
