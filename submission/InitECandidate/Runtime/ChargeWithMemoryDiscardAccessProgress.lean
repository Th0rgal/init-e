import InitECandidate.Runtime.ChargeWithMemoryAccessProgress
import InitECandidate.Runtime.ChargeWithMemoryDiscardProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed typed charged-memory call supplies a real bounded access
span and aligned stored length as well as strict global gas progress. -/
theorem charge_with_memory_discard_access_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (arguments : List (ExpHOL 64)) (base length capacity pointer scratch gasBase sa sb sc sd na nb nc nd : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word gasBase),fundingU256 sa sb sc sd,fundingU256 na nb nc nd])
 (currentAligned : length.toNat%32=0)
 (positive : 0<gasBase.toNat)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base) (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat) (frameExtent : current.address.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_with_memory") arguments)=(none,post)) :
 post.locals=s.locals ∧∃expansion total : BitVec 64,expansion.toNat<2^37 ∧gasBase.toNat≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current.charged total::ancestors)=interpreterFundingUsed (current::ancestors)+total.toNat ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 ∃newCapacity nextPointer : BitVec 64,
 post.memory (current.address+24)=.word base ∧post.memory (current.address+32)=.word (length+expansion) ∧post.memory (current.address+40)=.word newCapacity ∧
 (length+expansion).toNat≤newCapacity.toNat ∧(length+expansion).toNat%32=0 ∧
 (evmSatWord na nb nc nd≠0#64 → (evmSatWord sa sb sc sd).toNat+(evmSatWord na nb nc nd).toNat≤(length+expansion).toNat) ∧base.toNat+newCapacity.toNat≤nextPointer.toNat ∧
 pointer.toNat≤nextPointer.toNat ∧nextPointer.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "ev")=some (.val (.word current.address)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word nextPointer)) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 let start:=fundingU256 sa sb sc sd
 let size:=fundingU256 na nb nc nd
 have installed : s.code.lookup (ofString "charge_with_memory")=some ([(ofString "base",shapeOfHOLExact (.val (.word gasBase))),(ofString "start",shapeOfHOLExact start),(ofString "size",shapeOfHOLExact size)],sourceFunctionBody Guest.guestFn_charge_with_memory,.one) := by
  rw [code]
  simpa only [start,size,fundingU256,shapeOfHOLExact,List.map_cons,List.map_nil] using originalRuntimeCode_chargeWithMemory_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=((HolFiniteMapExact.empty.update (ofString "base",.val (.word gasBase))).update (ofString "start",start)).update (ofString "size",size)
 have lookup:=pan_three_shaped_value_lookup s.code.lookup (ofString "charge_with_memory") (ofString "base") (ofString "start") (ofString "size") (sourceFunctionBody Guest.guestFn_charge_with_memory) (.val (.word gasBase)) start size (by decide) (by decide) (by decide) installed
 obtain ⟨value,bodyPost,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "charge_with_memory") arguments _ _ callee .one args lookup run
 obtain ⟨other,otherPost,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "charge_with_memory") arguments _ _ callee .one args lookup run
 have same : otherPost=bodyPost:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherPost
 have atGasBase : (callEntryStateHOLFinite s callee).locals.lookup (ofString "base")=some (.val (.word gasBase)) := by
  simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atStart : (callEntryStateHOLFinite s callee).locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd) := by
  simp (config:={decide:=true}) [callee,start,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atSize : (callEntryStateHOLFinite s callee).locals.lookup (ofString "size")=some (fundingU256 na nb nc nd) := by
  simp [callee,size,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have entryLayout : InterpreterFundingLayout (callEntryStateHOLFinite s callee) current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 obtain ⟨_,expansion,total,small,baseBound,enough,preserved,used,progress,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,newLengthBound,newAligned,access,extent,mono,within,evKept,scratchKept,pointerKept,domain,endian,installedBody⟩:=charge_with_memory_body_access_progress (callEntryStateHOLFinite s callee) bodyPost upper current ancestors entryLayout base length capacity pointer scratch gasBase sa sb sc sd na nb nc nd value atGasBase atStart atSize currentAligned positive atFrame headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "charge_with_memory") arguments)
 rw [run] at metadata
 have postLayout : InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors):=preserved.after_memory memory (metadata.2.1.trans domain.symm)
 refine ⟨locals,expansion,total,small,baseBound,enough,postLayout,used,progress,newCapacity,nextPointer,?_,?_,?_,newLengthBound,newAligned,access,extent,mono,within,?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [memory];exact baseKept
 · rw [memory];exact lengthKept
 · rw [memory];exact capacityKept
 · rw [globals];exact evKept
 · rw [globals];exact scratchKept
 · rw [globals];exact pointerKept
#print axioms charge_with_memory_discard_access_progress
end InitECandidate.Runtime
