import InitECandidate.Runtime.ArithmeticChargedPhysicalContext
import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual complete original ADD/SUB/MUL normal bodies close a concrete next
physical opcode state and strictly funded progress through the real source. -/
theorem arithmetic_opcode_body_returned_physical_context
 (kind : ArithmeticOpcodeKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (value : ValueHOL 64)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (arithmeticOpcodeBody kind)=(some (.returned value),post)) :
 value=.val (.word 0) ∧arithmeticOpcodeFee kind≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged (arithmeticOpcodeFee kind)::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged (arithmeticOpcodeFee kind)::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_arithmetic_opcode_body kind,source_arithmetic_opcode_0 kind] at run
 obtain ⟨a,b,c,d,firstBody,firstOutput,firstRun,firstScope,firstPositive,firstPhysical,firstFunding,firstGlobals,firstDomain,firstEndian,firstCode,firstUpper⟩:=stack_pop_declaration_returned_physical_context s post upper current ancestors layout words valid (ofString "x") (arithmeticOpcodeAt kind 1) value code run
 let first:=setVarHOLFinite (ofString "x") (fundingU256 a b c d) {firstBody with locals:=s.locals}
 let firstWords : EvmMemoryOperandWords:={words with stackSize:=words.stackSize-1}
 change evaluateHOLFiniteState first (arithmeticOpcodeAt kind 1)=_ at firstRun
 change EvmMemoryOperandAt first current.address firstWords at firstPhysical
 change InterpreterFundingLayout first current.address.toNat upper (current::ancestors) at firstFunding
 change first.code=s.code at firstCode
 change first.memaddrs=s.memaddrs at firstDomain
 rw [source_arithmetic_opcode_1 kind] at firstRun
 obtain ⟨e,f,g,h,secondBody,secondOutput,secondRun,secondScope,secondPositive,secondPhysical,secondFunding,secondGlobals,secondDomain,secondEndian,secondCode,secondUpper⟩:=stack_pop_declaration_returned_physical_context first firstOutput upper current ancestors firstFunding firstWords firstPhysical (ofString "y") (arithmeticOpcodeAt kind 2) value (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "y") (fundingU256 e f g h) {secondBody with locals:=first.locals}
 let secondWords : EvmMemoryOperandWords:={firstWords with stackSize:=firstWords.stackSize-1}
 change evaluateHOLFiniteState second (arithmeticOpcodeAt kind 2)=_ at secondRun
 change EvmMemoryOperandAt second current.address secondWords at secondPhysical
 change InterpreterFundingLayout second current.address.toNat upper (current::ancestors) at secondFunding
 change second.code=first.code at secondCode
 change second.memaddrs=first.memaddrs at secondDomain
 have atX : second.locals.lookup (ofString "x")=some (fundingU256 a b c d) := by simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atY : second.locals.lookup (ofString "y")=some (fundingU256 e f g h) := by simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have decrement : (firstWords.stackSize-1#64).toNat=firstWords.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤firstWords.stackSize.toNat;change 1≤firstWords.stackSize.toNat;omega))
 have inside : secondWords.stackSize.toNat<secondWords.stackCapacity.toNat := by
  change (firstWords.stackSize-1#64).toNat<firstWords.stackCapacity.toNat
  rw [decrement]
  have previous:=firstPhysical.stackSizeBound
  omega
 obtain ⟨zero,enough,paid,progress,physical,globals,domain,endian,installed,upperFrame⟩:=arithmetic_charged_returned_physical_context kind second secondOutput upper current ancestors secondFunding secondWords secondPhysical a b c d e f g h value atX atY inside (by intro address below;rw [secondDomain,firstDomain];exact fullDomain address below) (secondCode.trans (firstCode.trans code)) secondRun
 have finalPhysical : EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1+1} := by
  apply EvmMemoryOperandAt.after_context (post:=post) physical
  · rw [firstScope,secondScope]
  · rw [firstScope,secondScope]
  · rw [firstScope,secondScope]
 have finalFunding : InterpreterFundingLayout post current.address.toNat upper (current.charged (arithmeticOpcodeFee kind)::ancestors):=paid.after_memory (by rw [firstScope,secondScope]) (by rw [firstScope,secondScope])
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,?_,?_,?_,?_,?_⟩
 · rw [firstScope,secondScope,globals];exact secondGlobals.trans firstGlobals
 · rw [firstScope,secondScope,domain,secondDomain,firstDomain]
 · rw [firstScope,secondScope,endian,secondEndian,firstEndian]
 · rw [firstScope,secondScope,installed,secondCode,firstCode]
 · intro watched above notPc notCounter notLeft notUsed
   rw [firstScope,secondScope,upperFrame watched above notPc notCounter notLeft notUsed,secondUpper watched notCounter,firstUpper watched notCounter]
#print axioms arithmetic_opcode_body_returned_physical_context
end InitECandidate.Runtime
