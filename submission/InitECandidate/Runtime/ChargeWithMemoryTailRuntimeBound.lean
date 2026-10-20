import InitECandidate.Runtime.ChargeWithMemoryTailFunding
import InitECandidate.Runtime.MemoryExtensionCallRuntimeBound
import InitECandidate.Runtime.VmFn_charge_gas
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual charge and extension tail includes out-of-gas and allocator/access
failure within its fixed source bound. Sufficient fee is derived on the actual
normal debit path, never assumed. -/
theorem charge_with_memory_tail_bounded
 (s : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity expansion pointer scratch fee total : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (atTotal : s.locals.lookup (ofString "total")=some (.val (.word total)))
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
 (budget : 1+(memoryExtensionBodyCost+1)≤s.clock) :
 RunBounded s (chargeWithMemoryAt 2) (1+(memoryExtensionBodyCost+1)) := by
 rw [source_charge_with_memory_2]
 have charge : RunBounded s (.call (some (none,none)) (ofString "charge_gas") [.var .local (ofString "total")]) 1 :=
  RunBounded.ofProg (ProgBounded.call vmBound_charge_gas none _) code (by omega)
 apply RunBounded.seq charge budget
 intro charged chargeRun chargedCode chargedBudget
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "total")]=some [.val (.word total)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTotal]
 obtain ⟨enough,chargedEq,funding,used,globals,clock,locals,_⟩:=charge_gas_discard_normal_funding s charged current.address.toNat upper current ancestors layout _ total args atFrame code chargeRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "charge_gas") [.var .local (ofString "total")])
 rw [chargeRun] at metadata
 have chargedFrame : charged.globals.lookup (ofString "ev")=some (.val (.word current.address)) := by rw [globals];exact atFrame
 have chargedPointer : charged.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)) := by rw [globals];exact atPointer
 have chargedScratch : charged.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) := by rw [globals];exact atScratch
 have chargedDomain : ∀offset∈([24,32,40] : List (BitVec 64)),charged.memaddrs (current.address+offset) := by
  intro offset member;rw [metadata.2.1];exact headerDomain offset member
 have chargedBase : charged.memory (current.address+24)=.word base := by
  rw [chargedEq];simpa [chargeGasCallPost,sourceWriteWord] using baseAt
 have chargedLength : charged.memory (current.address+32)=.word length := by
  rw [chargedEq];simpa [chargeGasCallPost,sourceWriteWord] using lengthAt
 have chargedCapacity : charged.memory (current.address+40)=.word capacity := by
  rw [chargedEq];simpa [chargeGasCallPost,sourceWriteWord] using capacityAt
 have extensionArgs : evalListHOLFinite charged (h:=fun a=>Classical.propDecidable (charged.memaddrs a)) [.rfield 1 (.var .local (ofString "x"))]=some [.val (.word expansion)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,atPair]
 have extension:=memory_extension_discard_call_bounded charged _ current.address base length capacity expansion pointer scratch chargedFrame extensionArgs chargedDomain chargedBase chargedLength chargedCapacity chargedPointer chargedScratch lengthOrder expansionBound oldExtent ordered belowFrame frameExtent (chargedCode.trans code) chargedBudget
 rw [source_charge_with_memory_3]
 have result:=RunBounded.seq extension (tail:=chargeWithMemoryAt 4) (b:=0) (by omega) (by
  intro next ran installed remaining
  exact RunBounded.ofProg (ProgBounded.straight (chargeWithMemoryAt 4) (by decide_cbv)) (installed.trans (chargedCode.trans code)) (by omega))
 simpa only [Nat.add_zero] using result
#print axioms charge_with_memory_tail_bounded
end InitECandidate.Runtime
