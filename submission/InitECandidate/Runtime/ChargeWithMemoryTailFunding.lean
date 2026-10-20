import InitECandidate.Runtime.InterpreterFundingMemoryTransport
import InitECandidate.Runtime.ChargeWithMemorySource
import InitECandidate.Runtime.ChargeGasDiscardNormalFunding
import InitECandidate.Runtime.InterpreterFundingMemoryExtension
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual charge_with_memory tail: charge sufficiency is derived from its
successful source run, then the original extension preserves every funding word. -/
theorem charge_with_memory_tail_returned_funding
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity expansion pointer scratch fee total : BitVec 64) (value : ValueHOL 64)
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
 (run : evaluateHOLFiniteState s (chargeWithMemoryAt 2)=(some (.returned value),post)) :
 value=.val (.word (0#64)) ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current.charged total::ancestors)=interpreterFundingUsed (current::ancestors)+total.toNat ∧
 ∃newCapacity nextPointer : BitVec 64,
 post.memory (current.address+24)=.word base ∧post.memory (current.address+32)=.word (length+expansion) ∧post.memory (current.address+40)=.word newCapacity ∧
 (length+expansion).toNat≤newCapacity.toNat ∧base.toNat+newCapacity.toNat≤nextPointer.toNat ∧
 pointer.toNat≤nextPointer.toNat ∧nextPointer.toNat≤scratch.toNat ∧
 post.globals.lookup (ofString "ev")=some (.val (.word current.address)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
 post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word nextPointer)) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [source_charge_with_memory_2] at run
 obtain ⟨charged,chargeRun,restRun⟩:=seq_returned_of_nonreturning_first
  (fun v=>discard_call_not_returned s (ofString "charge_gas") _ v) run
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
 rw [source_charge_with_memory_3] at restRun
 obtain ⟨extended,extensionRun,returnRun⟩:=seq_returned_of_nonreturning_first
  (fun v=>discard_call_not_returned charged (ofString "extend_memory") _ v) restRun
 obtain ⟨preserved,_,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,newLengthBound,extent,mono,within,evKept,scratchKept,pointerKept,_,domain,endian,installed⟩:=interpreter_funding_memory_extension_normal charged extended upper (current.charged total) ancestors funding _ base length capacity expansion pointer scratch chargedFrame extensionArgs chargedDomain chargedBase chargedLength chargedCapacity chargedPointer chargedScratch lengthOrder expansionBound oldExtent ordered belowFrame frameExtent (metadata.1.trans code) extensionRun
 rw [source_charge_with_memory_4] at returnRun
 have finalReturn : evaluateHOLFiniteState extended (.return (.const 0))=
  (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite extended) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
 obtain ⟨returned,postEq⟩:=Prod.mk.inj (returnRun.symm.trans finalReturn)
 refine ⟨PanSemResultExact.returned.inj (Option.some.inj returned),enough,?_,used,newCapacity,nextPointer,?_,?_,?_,newLengthBound,extent,mono,within,?_,?_,?_,?_,?_,?_⟩
 · rw [postEq];exact preserved.after_memory rfl rfl
 all_goals rw [postEq]
 · exact baseKept
 · exact lengthKept
 · exact capacityKept
 · exact evKept
 · exact scratchKept
 · exact pointerKept
 · exact domain.trans metadata.2.1
 · exact endian.trans metadata.2.2.1
 · exact installed.trans metadata.1
#print axioms charge_with_memory_tail_returned_funding
end InitECandidate.Runtime
