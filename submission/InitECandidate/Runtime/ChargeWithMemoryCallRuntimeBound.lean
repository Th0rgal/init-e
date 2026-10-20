import InitECandidate.Runtime.ChargeWithMemoryBodyRuntimeBound
import InitECandidate.Runtime.ChargeWithMemoryDiscardProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual original installed charged-memory discard call is quantitatively
bounded in every outcome, with its real shaped arguments and physical context. -/
theorem charge_with_memory_discard_call_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (arguments : List (ExpHOL 64)) (start size : ValueHOL 64) (base length capacity pointer scratch gasBase : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word gasBase),start,size])
 (startShape : shapeOfHOLExact start=.comb [.one,.one,.one,.one])
 (sizeShape : shapeOfHOLExact size=.comb [.one,.one,.one,.one])
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
 (budget : chargeWithMemoryBodyCost+1≤s.clock) :
 RunBounded s (.call (some (none,none)) (ofString "charge_with_memory") arguments) (chargeWithMemoryBodyCost+1) := by
 have installed : s.code.lookup (ofString "charge_with_memory")=some ([(ofString "base",shapeOfHOLExact (.val (.word gasBase))),(ofString "start",shapeOfHOLExact start),(ofString "size",shapeOfHOLExact size)],sourceFunctionBody Guest.guestFn_charge_with_memory,.one) := by
  rw [startShape,sizeShape,code]
  simpa only [shapeOfHOLExact] using originalRuntimeCode_chargeWithMemory_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=((HolFiniteMapExact.empty.update (ofString "base",.val (.word gasBase))).update (ofString "start",start)).update (ofString "size",size)
 have lookup:=pan_three_shaped_value_lookup s.code.lookup (ofString "charge_with_memory") (ofString "base") (ofString "start") (ofString "size") (sourceFunctionBody Guest.guestFn_charge_with_memory) (.val (.word gasBase)) start size (by decide) (by decide) (by decide) installed
 apply RunBounded.call args budget
 intro body locals returnShape found
 rw [lookup] at found
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj found.symm
 have atGasBase : (callEntryStateHOLFinite s callee).locals.lookup (ofString "base")=some (.val (.word gasBase)) := by
  simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atStart : (callEntryStateHOLFinite s callee).locals.lookup (ofString "start")=some start := by
  simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atSize : (callEntryStateHOLFinite s callee).locals.lookup (ofString "size")=some size := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have entryLayout : InterpreterFundingLayout (callEntryStateHOLFinite s callee) current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 exact charge_with_memory_body_bounded (callEntryStateHOLFinite s callee) upper current ancestors entryLayout start size base length capacity pointer scratch gasBase atFrame atGasBase atStart atSize headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent code (by change chargeWithMemoryBodyCost≤s.clock-1;omega)
#print axioms charge_with_memory_discard_call_bounded
end InitECandidate.Runtime
