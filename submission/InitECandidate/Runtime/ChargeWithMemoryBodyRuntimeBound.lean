import InitECandidate.Runtime.ChargeWithMemoryFeeRuntimeBound
import InitECandidate.Runtime.MemoryCostOneReturnedSizeBound
import InitECandidate.Runtime.VmFn_extend_memory_cost1
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
def chargeWithMemoryBodyCost : Nat:=20+1+(1+(1+(memoryExtensionBodyCost+1)))
/-- Whole original charged-memory helper has a fixed concrete all-outcome
source bound. Actual cost1 returns its expansion ceiling and actual read-only
metadata; failed argument lookup, gas charge, allocation and access all terminate.
No successful callee/fee/runtime/frame premise is assumed. -/
theorem charge_with_memory_body_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (start size : ValueHOL 64) (base length capacity pointer scratch gasBase : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (atGasBase : s.locals.lookup (ofString "base")=some (.val (.word gasBase)))
 (atStart : s.locals.lookup (ofString "start")=some start)
 (atSize : s.locals.lookup (ofString "size")=some size)
 (headerDomain : ∀offset∈([24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base) (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat) (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat) (frameExtent : current.address.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode)
 (budget : chargeWithMemoryBodyCost≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_charge_with_memory) (chargeWithMemoryBodyCost) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "start"),.var .local (ofString "size")]=some [start,size] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atStart,atSize]
 have installed : s.code.lookup (ofString "extend_memory_cost1")=some ([(ofString "start",.comb [.one,.one,.one,.one]),(ofString "size",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_extend_memory_cost1,.comb [.one,.one]) := by
  rw [code];exact vmLookup_extend_memory_cost1
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (chargeWithMemoryAt 0) _
 rw [source_charge_with_memory_0]
 apply RunBounded.decCall args budget
 intro body locals returnShape found
 have bodyEq:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "extend_memory_cost1") _ (sourceFunctionBody Guest.guestFn_extend_memory_cost1) body (.comb [.one,.one]) returnShape [start,size] locals installed found
 subst body
 refine ⟨?_,?_⟩
 · exact ProgBounded.bodies_of_fun vmBound_extend_memory_cost1 s code (by unfold chargeWithMemoryBodyCost at budget;omega) [start,size] _ locals returnShape found
 · intro value post bodyRun remaining
   have frame:=memoryFrame_of_good vmLookup_extend_memory_cost1 (by decide) (by decide) (callEntryStateHOLFinite s locals) code
   have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s locals) (sourceFunctionBody Guest.guestFn_extend_memory_cost1)
   rw [bodyRun] at frame metadata
   obtain ⟨fee,expansion,valueEq,small⟩:=memory_cost_one_returned_size_bound (callEntryStateHOLFinite s locals) post value code bodyRun
   subst value
   let ready:=setVarHOLFinite (ofString "x") (.rStruct [.val (.word fee),.val (.word expansion)]) {post with locals:=s.locals}
   change RunBounded ready (chargeWithMemoryAt 1) _
   have sameMemory : ready.memory=s.memory:=frame.1
   have sameGlobals : ready.globals=s.globals:=frame.2
   have sameDomain : ready.memaddrs=s.memaddrs:=metadata.2.1
   have nextLayout : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=layout.after_memory sameMemory sameDomain
   have nextFrame : ready.globals.lookup (ofString "ev")=some (.val (.word current.address)) := by rw [sameGlobals];exact atFrame
   have nextGasBase : ready.locals.lookup (ofString "base")=some (.val (.word gasBase)) := by
    simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atGasBase
   have nextPair : ready.locals.lookup (ofString "x")=some (.rStruct [.val (.word fee),.val (.word expansion)]) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   have nextDomain : ∀offset∈([24,32,40] : List (BitVec 64)),ready.memaddrs (current.address+offset) := by
    intro offset member;rw [sameDomain];exact headerDomain offset member
   have nextBase : ready.memory (current.address+24)=.word base := by rw [sameMemory];exact baseAt
   have nextLength : ready.memory (current.address+32)=.word length := by rw [sameMemory];exact lengthAt
   have nextCapacity : ready.memory (current.address+40)=.word capacity := by rw [sameMemory];exact capacityAt
   have nextPointer : ready.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)) := by rw [sameGlobals];exact atPointer
   have nextScratch : ready.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) := by rw [sameGlobals];exact atScratch
   exact charge_with_memory_fee_suffix_bounded ready upper current ancestors nextLayout base length capacity expansion pointer scratch fee gasBase nextFrame nextGasBase nextPair nextDomain nextBase nextLength nextCapacity nextPointer nextScratch lengthOrder (by omega) oldExtent ordered belowFrame frameExtent (metadata.1.trans code) remaining
#print axioms charge_with_memory_body_bounded
end InitECandidate.Runtime
