import InitECandidate.Runtime.NotChargedPhysicalContext
import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Actual complete original NOT normal body closes a concrete next physical
opcode state and strictly funded progress through the real source. -/
theorem not_opcode_body_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (value : ValueHOL 64)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s notOpcodeBody=(some (.returned value),post)) :
 value=.val (.word 0) ∧notOpcodeFee≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged notOpcodeFee::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged notOpcodeFee::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_not_opcode_body,source_not_opcode_0] at run
 obtain ⟨a,b,c,d,firstBody,firstOutput,firstRun,firstScope,firstPositive,firstPhysical,firstFunding,firstGlobals,firstDomain,firstEndian,firstCode,firstUpper⟩:=stack_pop_declaration_returned_physical_context s post upper current ancestors layout words valid (ofString "x") (notOpcodeAt 1) value code run
 let first:=setVarHOLFinite (ofString "x") (fundingU256 a b c d) {firstBody with locals:=s.locals}
 let firstWords : EvmMemoryOperandWords:={words with stackSize:=words.stackSize-1}
 change evaluateHOLFiniteState first (notOpcodeAt 1)=_ at firstRun
 change EvmMemoryOperandAt first current.address firstWords at firstPhysical
 change InterpreterFundingLayout first current.address.toNat upper (current::ancestors) at firstFunding
 change first.code=s.code at firstCode
 change first.memaddrs=s.memaddrs at firstDomain
 have atX : first.locals.lookup (ofString "x")=some (fundingU256 a b c d) := by simp (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have decrement : (words.stackSize-1#64).toNat=words.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤words.stackSize.toNat;change 1≤words.stackSize.toNat;omega))
 have inside : firstWords.stackSize.toNat<firstWords.stackCapacity.toNat := by
  change (words.stackSize-1#64).toNat<words.stackCapacity.toNat
  rw [decrement]
  have previous:=valid.stackSizeBound
  omega
 obtain ⟨zero,enough,paid,progress,physical,globals,domain,endian,installed,upperFrame⟩:=not_charged_returned_physical_context first firstOutput upper current ancestors firstFunding firstWords firstPhysical a b c d value atX inside (by intro address below;rw [firstDomain];exact fullDomain address below) (firstCode.trans code) firstRun
 have finalPhysical : EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)+1} := by
  apply EvmMemoryOperandAt.after_context (post:=post) physical
  · rw [firstScope]
  · rw [firstScope]
  · rw [firstScope]
 have finalFunding : InterpreterFundingLayout post current.address.toNat upper (current.charged notOpcodeFee::ancestors):=paid.after_memory (by rw [firstScope]) (by rw [firstScope])
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,?_,?_,?_,?_,?_⟩
 · rw [firstScope,globals];exact firstGlobals
 · rw [firstScope,domain,firstDomain]
 · rw [firstScope,endian,firstEndian]
 · rw [firstScope,installed,firstCode]
 · intro watched above notPc notCounter notLeft notUsed
   rw [firstScope,upperFrame watched above notPc notCounter notLeft notUsed,firstUpper watched notCounter]
#print axioms not_opcode_body_returned_physical_context
end InitECandidate.Runtime
