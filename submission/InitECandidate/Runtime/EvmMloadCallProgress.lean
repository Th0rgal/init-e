import InitECandidate.Runtime.EvmMloadBodyProgress
import InitECandidate.Runtime.OriginalMloadCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem mload_discard_normal_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base index capacity scratch pointer pc memoryBase memoryLength memoryCapacity : BitVec 64)
 (currentAligned : memoryLength.toNat%32=0)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([0,8,16,24,32,40,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base)
 (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (memoryAt : s.memory (current.address+24)=.word memoryBase)
 (lengthAt : s.memory (current.address+32)=.word memoryLength)
 (memoryCapacityAt : s.memory (current.address+40)=.word memoryCapacity)
 (pcAt : s.memory (current.address+0)=.word pc)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : memoryLength.toNat≤memoryCapacity.toNat)
 (oldExtent : memoryBase.toNat+memoryCapacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat) (belowFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "op_mload") [])=(none,post)) :
 post.locals=s.locals ∧∃total : BitVec 64,3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) := by
 have installed : s.code.lookup (ofString "op_mload")=some ([],sourceFunctionBody Guest.guestFn_op_mload,.one) := by rw [code];exact originalRuntimeCode_opMload_lookup
 have lookup:=pan_no_args_shape_lookup s.code.lookup (ofString "op_mload") (sourceFunctionBody Guest.guestFn_op_mload) .one installed
 obtain ⟨returned,output,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "op_mload") [] [] (sourceFunctionBody Guest.guestFn_op_mload) HolFiniteMapExact.empty .one rfl lookup run
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have entryLayout : InterpreterFundingLayout entry current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 obtain ⟨zero,total,baseBound,enough,paid,progress⟩:=mload_body_returned_progress entry output upper current ancestors entryLayout base index capacity scratch pointer pc memoryBase memoryLength memoryCapacity returned currentAligned atFrame headerDomain baseAt indexAt capacityAt memoryAt lengthAt memoryCapacityAt pcAt positive capacityBound indexBound bufferExtent atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent fullDomain code bodyRun
 refine ⟨locals,total,baseBound,enough,?_,progress⟩
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "op_mload") [])
 rw [run] at metadata
 have bodyMetadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_op_mload)
 rw [bodyRun] at bodyMetadata
 exact paid.after_memory memory (metadata.2.1.trans bodyMetadata.2.1.symm)
#print axioms mload_discard_normal_progress
end InitECandidate.Runtime
