import InitECandidate.Runtime.MemoryStoreChargedPhysicalContext
import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- The complete original byte/word MSTORE bodies: both actual checked pops,
charge, source writer and final PC/return close the next physical opcode state. -/
theorem memory_store_body_returned_physical_context
 (kind : MemoryStorePhysicalKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (value : ValueHOL 64) (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (memoryStorePhysicalBody kind)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃expansion total newCapacity nextPointer : BitVec 64,
 3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,words.scratchPointer.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+32→watched≠current.address+40→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_memory_store_physical_body,source_memory_store_physical_0] at run
 obtain ⟨sa,sb,sc,sd,firstBody,firstOutput,firstRun,firstScope,firstPositive,firstPhysical,firstFunding,firstGlobals,firstDomain,firstEndian,firstCode,firstUpper⟩:=stack_pop_declaration_returned_physical_context s post upper current ancestors layout words valid (ofString "start") (memoryStorePhysicalAt kind 1) value code run
 let first:=setVarHOLFinite (ofString "start") (fundingU256 sa sb sc sd) {firstBody with locals:=s.locals}
 let firstWords : EvmMemoryOperandWords:={words with stackSize:=words.stackSize-1}
 change evaluateHOLFiniteState first (memoryStorePhysicalAt kind 1)=_ at firstRun
 change EvmMemoryOperandAt first current.address firstWords at firstPhysical
 change InterpreterFundingLayout first current.address.toNat upper (current::ancestors) at firstFunding
 change first.code=s.code at firstCode
 change first.memaddrs=s.memaddrs at firstDomain
 rw [source_memory_store_physical_1] at firstRun
 obtain ⟨a,b,c,d,secondBody,secondOutput,secondRun,secondScope,secondPositive,secondPhysical,secondFunding,secondGlobals,secondDomain,secondEndian,secondCode,secondUpper⟩:=stack_pop_declaration_returned_physical_context first firstOutput upper current ancestors firstFunding firstWords firstPhysical (ofString "value") (memoryStorePhysicalAt kind 2) value (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "value") (fundingU256 a b c d) {secondBody with locals:=first.locals}
 let secondWords : EvmMemoryOperandWords:={firstWords with stackSize:=firstWords.stackSize-1}
 change evaluateHOLFiniteState second (memoryStorePhysicalAt kind 2)=_ at secondRun
 change EvmMemoryOperandAt second current.address secondWords at secondPhysical
 change InterpreterFundingLayout second current.address.toNat upper (current::ancestors) at secondFunding
 change second.code=first.code at secondCode
 change second.memaddrs=first.memaddrs at secondDomain
 have startAt : second.locals.lookup (ofString "start")=some (fundingU256 sa sb sc sd) := by simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have valueAt : second.locals.lookup (ofString "value")=some (fundingU256 a b c d) := by simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,paid,progress,physical,domain,endian,installed,upperFrame⟩:=memory_store_charged_returned_physical_context kind second secondOutput upper current ancestors secondFunding secondWords secondPhysical sa sb sc sd a b c d value startAt valueAt (secondCode.trans (firstCode.trans code)) (by rw [secondDomain,firstDomain];exact domOK) secondRun
 have finalPhysical : EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1,memoryLength:=words.memoryLength+expansion,memoryCapacity:=newCapacity,framePointer:=nextPointer} := by
  apply EvmMemoryOperandAt.after_context (post:=post) physical
  · rw [firstScope,secondScope]
  · rw [firstScope,secondScope]
  · rw [firstScope,secondScope]
 have finalFunding : InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors):=paid.after_memory (by rw [firstScope,secondScope]) (by rw [firstScope,secondScope])
 refine ⟨zero,expansion,total,newCapacity,nextPointer,baseBound,enough,finalFunding,progress,finalPhysical,?_,?_,?_,?_⟩
 · rw [firstScope,secondScope,domain,secondDomain,firstDomain]
 · rw [firstScope,secondScope,endian,secondEndian,firstEndian]
 · rw [firstScope,secondScope,installed,secondCode,firstCode]
 · intro watched above notPc notCounter notLength notCapacity notLeft notUsed
   rw [firstScope,secondScope,upperFrame watched above notPc notLength notCapacity notLeft notUsed,secondUpper watched notCounter,firstUpper watched notCounter]
#print axioms memory_store_body_returned_physical_context
end InitECandidate.Runtime
