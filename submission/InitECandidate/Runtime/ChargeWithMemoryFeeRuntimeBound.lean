import InitECandidate.Runtime.ChargeWithMemoryTailRuntimeBound
import InitECandidate.Runtime.AddSatDeclarationRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Exact original saturating fee declaration followed by actual charged-memory
tail, all outcomes included under concrete initial ownership. -/
theorem charge_with_memory_fee_suffix_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity expansion pointer scratch fee gasBase : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (atGasBase : s.locals.lookup (ofString "base")=some (.val (.word gasBase)))
 (atPair : s.locals.lookup (ofString "x")=some (.rStruct [.val (.word fee),.val (.word expansion)]))
 (headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base) (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat) (expansionBound : expansion.toNat<2^38)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat) (frameExtent : current.address.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode)
 (budget : 1+(1+(memoryExtensionBodyCost+1))≤s.clock) :
 RunBounded s (chargeWithMemoryAt 1) (1+(1+(memoryExtensionBodyCost+1))) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "base"),.rfield 0 (.var .local (ofString "x"))]=some [.val (.word gasBase),.val (.word fee)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atGasBase,atPair]
 let total:=wordAddSat gasBase fee
 let ready:=setVarHOLFinite (ofString "total") (.val (.word total)) {s with clock:=s.clock-1}
 have nextLayout : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=layout.after_memory rfl rfl
 have nextTotal : ready.locals.lookup (ofString "total")=some (.val (.word total)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have nextPair : ready.locals.lookup (ofString "x")=some (.rStruct [.val (.word fee),.val (.word expansion)]) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPair
 have bounded:=charge_with_memory_tail_bounded ready upper current ancestors nextLayout base length capacity expansion pointer scratch fee total atFrame nextTotal nextPair headerDomain baseAt lengthAt capacityAt atPointer atScratch lengthOrder expansionBound oldExtent ordered belowFrame frameExtent code (by change 1+(memoryExtensionBodyCost+1)≤s.clock-1;omega)
 rw [source_charge_with_memory_1]
 exact runBounded_add_sat_declaration s (ofString "total") _ (chargeWithMemoryAt 2) gasBase fee (1+(memoryExtensionBodyCost+1)) args code budget bounded
#print axioms charge_with_memory_fee_suffix_bounded
end InitECandidate.Runtime
