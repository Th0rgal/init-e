import InitECandidate.Runtime.EvmMstore8BodyProgress
import InitECandidate.Runtime.OriginalMstore8Code
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed dispatch-style MSTORE8 call strictly increases actual used
gas and preserves all live frame funding; initial concrete ownership is explicit. -/
theorem mstore8_discard_normal_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity pointer scratch pc index : BitVec 64)
 (currentAligned : length.toNat%32=0)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([0,16,24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base)
 (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (pcAt : s.memory (current.address+0)=.word pc)
 (indexAt : s.memory (current.address+16)=.word index)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "op_mstore8") [])=(none,post)) :
 post.locals=s.locals ∧∃total : BitVec 64,3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) := by
 have installed : s.code.lookup (ofString "op_mstore8")=some ([],sourceFunctionBody Guest.guestFn_op_mstore8,.one) := by rw [code];exact originalRuntimeCode_opMstore8_lookup
 have lookup:=pan_no_args_shape_lookup s.code.lookup (ofString "op_mstore8") (sourceFunctionBody Guest.guestFn_op_mstore8) .one installed
 obtain ⟨returned,output,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "op_mstore8") [] [] (sourceFunctionBody Guest.guestFn_op_mstore8) HolFiniteMapExact.empty .one rfl lookup run
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have entryLayout : InterpreterFundingLayout entry current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 obtain ⟨zero,total,baseBound,enough,paid,progress⟩:=mstore8_body_returned_progress entry output upper current ancestors entryLayout base length capacity pointer scratch pc index returned currentAligned atFrame headerDomain baseAt lengthAt capacityAt pcAt indexAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent code bodyRun
 refine ⟨locals,total,baseBound,enough,?_,progress⟩
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "op_mstore8") [])
 rw [run] at metadata
 have bodyMetadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_op_mstore8)
 rw [bodyRun] at bodyMetadata
 exact paid.after_memory memory (metadata.2.1.trans bodyMetadata.2.1.symm)
#print axioms mstore8_discard_normal_progress
end InitECandidate.Runtime
