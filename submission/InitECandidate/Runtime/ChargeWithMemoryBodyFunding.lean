import InitECandidate.Runtime.ChargeWithMemoryTailFunding
import InitECandidate.Runtime.MemoryCostOneBoundedDeclaration
import InitECandidate.Runtime.MemoryCostPureDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Whole original charge_with_memory, deriving the actual cost1 tuple and
scalar add_sat result through real declarations before the actual debit and
extension. No argument-typing, fee-sufficiency, or callee/frame callback. -/
theorem charge_with_memory_body_returned_funding
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity pointer scratch : BitVec 64) (value : ValueHOL 64)
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
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_charge_with_memory)=(some (.returned value),post)) :
 value=.val (.word (0#64)) ∧∃expansion total : BitVec 64,expansion.toNat<2^37 ∧total≤current.gas.left ∧
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
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (chargeWithMemoryAt 0)=_ at run
 rw [source_charge_with_memory_0] at run
 obtain ⟨fee,expansion,firstBody,firstOutput,firstRun,firstScope,nonwrap,small,firstMemory,firstGlobals,firstCode,firstDomain,firstEndian⟩:=memory_cost_one_bounded_declaration_returned s post (ofString "x") _ (chargeWithMemoryAt 1) current.address length value atFrame (headerDomain 32 (by simp)) lengthAt code run
 let first:=setVarHOLFinite (ofString "x") (.rStruct [.val (.word fee),.val (.word expansion)]) {firstBody with locals:=s.locals}
 change evaluateHOLFiniteState first (chargeWithMemoryAt 1)=_ at firstRun
 rw [source_charge_with_memory_1] at firstRun
 obtain ⟨total,secondBody,secondOutput,secondRun,secondScope,secondMemory,secondGlobals,secondCode,secondDomain,secondEndian⟩:=memory_cost_pure_declaration_returned first firstOutput (ofString "total") (ofString "add_sat") _ (chargeWithMemoryAt 2) value (firstCode.trans code) (by decide) (by decide) firstRun
 let second:=setVarHOLFinite (ofString "total") (.val (.word total)) {secondBody with locals:=first.locals}
 change evaluateHOLFiniteState second (chargeWithMemoryAt 2)=_ at secondRun
 have sameMemory : second.memory=s.memory:=secondMemory.trans firstMemory
 have sameGlobals : second.globals=s.globals:=secondGlobals.trans firstGlobals
 have sameDomain : second.memaddrs=s.memaddrs:=secondDomain.trans firstDomain
 have sameCode : second.code=originalRuntimeCode:=(secondCode.trans firstCode).trans code
 have nextLayout : InterpreterFundingLayout second current.address.toNat upper (current::ancestors):=layout.after_memory sameMemory sameDomain
 have nextFrame : second.globals.lookup (ofString "ev")=some (.val (.word current.address)) := by rw [sameGlobals];exact atFrame
 have nextPointerAt : second.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)) := by rw [sameGlobals];exact atPointer
 have nextScratch : second.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) := by rw [sameGlobals];exact atScratch
 have nextTotal : second.locals.lookup (ofString "total")=some (.val (.word total)) := by
  simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have nextPair : second.locals.lookup (ofString "x")=some (.rStruct [.val (.word fee),.val (.word expansion)]) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have nextDomain : ∀offset∈([24,32,40] : List (BitVec 64)),second.memaddrs (current.address+offset) := by
  intro offset member;rw [sameDomain];exact headerDomain offset member
 have nextBase : second.memory (current.address+24)=.word base:=by rw [sameMemory];exact baseAt
 have nextLength : second.memory (current.address+32)=.word length:=by rw [sameMemory];exact lengthAt
 have nextCapacity : second.memory (current.address+40)=.word capacity:=by rw [sameMemory];exact capacityAt
 obtain ⟨returned,enough,preserved,used,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,newLengthBound,extent,mono,within,evKept,scratchKept,pointerKept,domain,endian,installed⟩:=charge_with_memory_tail_returned_funding second secondOutput upper current ancestors nextLayout base length capacity expansion pointer scratch fee total value nextFrame nextTotal nextPair nextDomain nextBase nextLength nextCapacity nextPointerAt nextScratch lengthOrder (by omega) oldExtent ordered belowFrame frameExtent sameCode secondRun
 rw [firstScope,secondScope]
 refine ⟨returned,expansion,total,small,enough,preserved.after_memory rfl rfl,used,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,newLengthBound,extent,mono,within,evKept,scratchKept,pointerKept,?_,?_,?_⟩
 · exact domain.trans sameDomain
 · exact endian.trans (secondEndian.trans firstEndian)
 · exact installed.trans (secondCode.trans firstCode)
#print axioms charge_with_memory_body_returned_funding
end InitECandidate.Runtime
