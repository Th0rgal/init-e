import InitECandidate.Runtime.MloadChargedPhysicalContext
import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Complete original MLOAD: actual pop implies a free operand slot, so the
real read/push restores its old index, while funded progress and the dynamic
memory/operand context close for another real opcode. -/
theorem mload_body_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (value : ValueHOL 64)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_op_mload)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃expansion total newCapacity nextPointer : BitVec 64,
 3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (mloadAt 0)=_ at run
 rw [source_mload_0] at run
 obtain ⟨sa,sb,sc,sd,body,output,tail,scope,positive,physical,funding,globals,domain,endian,installed,upperFrame⟩:=stack_pop_declaration_returned_physical_context s post upper current ancestors layout words valid (ofString "start") (mloadAt 1) value code run
 let ready:=setVarHOLFinite (ofString "start") (fundingU256 sa sb sc sd) {body with locals:=s.locals}
 let readyWords : EvmMemoryOperandWords:={words with stackSize:=words.stackSize-1}
 change evaluateHOLFiniteState ready (mloadAt 1)=_ at tail
 change EvmMemoryOperandAt ready current.address readyWords at physical
 change InterpreterFundingLayout ready current.address.toNat upper (current::ancestors) at funding
 change ready.memaddrs=s.memaddrs at domain
 change ready.code=s.code at installed
 have decrement : (words.stackSize-1#64).toNat=words.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤words.stackSize.toNat;change 1≤words.stackSize.toNat;omega))
 have inside : readyWords.stackSize.toNat<readyWords.stackCapacity.toNat := by
  change (words.stackSize-1#64).toNat<words.stackCapacity.toNat
  rw [decrement]
  have bound:=valid.stackSizeBound
  omega
 have increment : ((words.stackSize-1#64)+1#64).toNat=(words.stackSize-1#64).toNat+1 := by
  rw [BitVec.toNat_add_of_lt (by rw [decrement];change words.stackSize.toNat-1+1<2^64;have first:=valid.stackSizeBound;have second:=valid.stackCapacityBound;omega)]
  rfl
 have restored : (words.stackSize-1#64)+1#64=words.stackSize := by
  apply BitVec.eq_of_toNat_eq
  rw [increment,decrement]
  omega
 obtain ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,finalPhysical,finalDomain,finalEndian,finalCode,finalFrame⟩:=mload_charged_returned_physical_context ready output upper current ancestors funding readyWords physical sa sb sc sd value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [domain];exact fullDomain address below) (installed.trans code) tail
 change EvmMemoryOperandAt output current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1#64)+1#64,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} at finalPhysical
 rw [restored] at finalPhysical
 have postPhysical : EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer}:=finalPhysical.after_context (by rw [scope]) (by rw [scope]) (by rw [scope])
 refine ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,paid.after_memory (by rw [scope]) (by rw [scope]),progress,postPhysical,?_,?_,?_,?_⟩
 · rw [scope,finalDomain,domain]
 · rw [scope,finalEndian,endian]
 · rw [scope,finalCode,installed]
 · intro watched above notPc notCounter notLength notCapacity notLeft notUsed
   rw [scope,finalFrame watched above notPc notCounter notLength notCapacity notLeft notUsed,upperFrame watched notCounter]
#print axioms mload_body_returned_physical_context
end InitECandidate.Runtime
