import InitECandidate.Runtime.ChargeWithMemoryBodyUpperFrame
import InitECandidate.Runtime.ChargeWithMemoryDiscardProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual installed charged-memory discard call protects all old controls and
operand-stack metadata outside the exact ev32/40/64/184 footprint. -/
theorem charge_with_memory_discard_upper_frame
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (arguments : List (ExpHOL 64)) (start size : ValueHOL 64) (base length capacity pointer scratch gasBase watched : BitVec 64)
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
 (above : scratch.toNat≤watched.toNat)
 (notLength : watched≠current.address+32) (notCapacity : watched≠current.address+40)
 (notLeft : watched≠current.address+64) (notUsed : watched≠current.address+184)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_with_memory") arguments)=(none,post)) :
 post.memory watched=s.memory watched := by
 have installed : s.code.lookup (ofString "charge_with_memory")=some ([(ofString "base",shapeOfHOLExact (.val (.word gasBase))),(ofString "start",shapeOfHOLExact start),(ofString "size",shapeOfHOLExact size)],sourceFunctionBody Guest.guestFn_charge_with_memory,.one) := by
  rw [startShape,sizeShape,code]
  simpa only [shapeOfHOLExact] using originalRuntimeCode_chargeWithMemory_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=((HolFiniteMapExact.empty.update (ofString "base",.val (.word gasBase))).update (ofString "start",start)).update (ofString "size",size)
 have lookup:=pan_three_shaped_value_lookup s.code.lookup (ofString "charge_with_memory") (ofString "base") (ofString "start") (ofString "size") (sourceFunctionBody Guest.guestFn_charge_with_memory) (.val (.word gasBase)) start size (by decide) (by decide) (by decide) installed
 obtain ⟨value,bodyPost,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "charge_with_memory") arguments _ _ callee .one args lookup run
 have entryLayout : InterpreterFundingLayout (callEntryStateHOLFinite s callee) current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 have framed:=charge_with_memory_body_upper_frame (callEntryStateHOLFinite s callee) bodyPost upper current ancestors entryLayout base length capacity pointer scratch watched value atFrame headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder oldExtent ordered belowFrame frameExtent above notLength notCapacity notLeft notUsed code bodyRun
 rw [memory]
 exact framed
#print axioms charge_with_memory_discard_upper_frame
end InitECandidate.Runtime
