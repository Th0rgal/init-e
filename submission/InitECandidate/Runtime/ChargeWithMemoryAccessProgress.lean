import InitECandidate.Runtime.MemoryCostOneAccessDeclaration
import InitECandidate.Runtime.ChargeWithMemoryTailFunding
import InitECandidate.Runtime.MemoryCostOneBoundedDeclaration
import InitECandidate.Runtime.AddSatReturnedExactContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Whole original charge_with_memory, deriving the actual cost1 tuple and
scalar add_sat result through real declarations before the actual debit and
extension. Typed positive base gas yields actual strict global used-gas progress and actual covered access span/aligned stored memory length. No fee-sufficiency or callee/frame callback. -/
theorem charge_with_memory_body_access_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity pointer scratch gasBase sa sb sc sd na nb nc nd : BitVec 64) (value : ValueHOL 64)
 (atGasBase : s.locals.lookup (ofString "base")=some (.val (.word gasBase)))
 (atStart : s.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd))
 (atSize : s.locals.lookup (ofString "size")=some (fundingU256 na nb nc nd))
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
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_charge_with_memory)=(some (.returned value),post)) :
 value=.val (.word (0#64)) ∧∃expansion total : BitVec 64,expansion.toNat<2^37 ∧gasBase.toNat≤total.toNat ∧total≤current.gas.left ∧
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
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (chargeWithMemoryAt 0)=_ at run
 rw [source_charge_with_memory_0] at run
 have inputArgs : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "start"),.var .local (ofString "size")]=some [fundingU256 sa sb sc sd,fundingU256 na nb nc nd] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atStart,atSize]
 obtain ⟨fee,expansion,firstBody,firstOutput,firstRun,firstScope,nonwrap,small,expansionAligned,span,firstMemory,firstGlobals,firstCode,firstDomain,firstEndian⟩:=memory_cost_one_access_declaration_returned s post (ofString "x") _ (chargeWithMemoryAt 1) current.address length sa sb sc sd na nb nc nd value inputArgs atFrame (headerDomain 32 (by simp)) lengthAt currentAligned code run
 let first:=setVarHOLFinite (ofString "x") (.rStruct [.val (.word fee),.val (.word expansion)]) {firstBody with locals:=s.locals}
 change evaluateHOLFiniteState first (chargeWithMemoryAt 1)=_ at firstRun
 rw [source_charge_with_memory_1] at firstRun
 have firstBase : first.locals.lookup (ofString "base")=some (.val (.word gasBase)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atGasBase
 have firstPair : first.locals.lookup (ofString "x")=some (.rStruct [.val (.word fee),.val (.word expansion)]) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have addArgs : evalListHOLFinite first (h:=fun a=>Classical.propDecidable (first.memaddrs a)) [.var .local (ofString "base"),.rfield 0 (.var .local (ofString "x"))]=some [.val (.word gasBase),.val (.word fee)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,firstBase,firstPair]
 obtain ⟨secondOutput,secondRun,secondScope⟩:=add_sat_returned_exact_context first firstOutput (ofString "total") _ gasBase fee (chargeWithMemoryAt 2) value addArgs (firstCode.trans code) firstRun
 let total:=wordAddSat gasBase fee
 let second:=setVarHOLFinite (ofString "total") (.val (.word total)) {first with clock:=first.clock-1}
 change evaluateHOLFiniteState second (chargeWithMemoryAt 2)=_ at secondRun
 have sameMemory : second.memory=s.memory:=firstMemory
 have sameGlobals : second.globals=s.globals:=firstGlobals
 have sameDomain : second.memaddrs=s.memaddrs:=firstDomain
 have sameCode : second.code=originalRuntimeCode:=firstCode.trans code
 have baseBound : gasBase.toNat≤total.toNat := by
  change gasBase.toNat≤(wordAddSat gasBase fee).toNat
  rw [wordAddSat_toNat]
  have within:=gasBase.isLt
  omega
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
 have leftBound : current.gas.left.toNat≤200000000 := by
  have bound:=layout.budget
  change current.gas.potential+interpreterFundingPotential ancestors≤200000000 at bound
  unfold GasFunding.potential at bound
  omega
 have feeBelow : fee.toNat≤total.toNat := by
  change fee.toNat≤(wordAddSat gasBase fee).toNat
  rw [wordAddSat_toNat]
  have within:=fee.isLt
  omega
 have notMaximum : fee≠18446744073709551615#64 := by
  intro maximum
  have enoughNat:=BitVec.le_def.mp enough
  rw [maximum] at feeBelow
  change 18446744073709551615≤total.toNat at feeBelow
  omega
 have sumNatural : (length+expansion).toNat=length.toNat+expansion.toNat:=BitVec.toNat_add_of_lt nonwrap
 have newAligned : (length+expansion).toNat%32=0 := by rw [sumNatural];omega
 have access (nonempty : evmSatWord na nb nc nd≠0#64) : (evmSatWord sa sb sc sd).toNat+(evmSatWord na nb nc nd).toNat≤(length+expansion).toNat := by
  rw [sumNatural]
  exact span notMaximum nonempty
 rw [firstScope,secondScope]
 refine ⟨returned,expansion,total,small,baseBound,enough,preserved.after_memory rfl rfl,used,by omega,newCapacity,nextPointer,baseKept,lengthKept,capacityKept,newLengthBound,newAligned,access,extent,mono,within,evKept,scratchKept,pointerKept,?_,?_,?_⟩
 · exact domain.trans sameDomain
 · exact endian.trans firstEndian
 · exact installed.trans firstCode
#print axioms charge_with_memory_body_access_progress
end InitECandidate.Runtime
