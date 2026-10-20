import InitECandidate.Runtime.ComparisonHelperFrame
import InitECandidate.Runtime.StackPushCallPhysicalContext
import InitECandidate.Runtime.InterpreterFundingOffsetFrame
import InitECandidate.Runtime.ChargeGasPhysicalContext
import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- The actual complete original `op_iszero` body: one real pop, the literal
charge, the installed `u256_is_zero` helper returning a checked word, the
boolean push and the PC/return close a concrete next physical opcode state
with strictly funded progress. -/
theorem zero_opcode_body_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (room : words.stackSize.toNat<words.stackCapacity.toNat)
 (value : ValueHOL 64)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s zeroOpcodeBody=(some (.returned value),post)) :
 value=.val (.word 0) ∧zeroOpcodeFee≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged zeroOpcodeFee::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged zeroOpcodeFee::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_zero_opcode_body,source_zero_opcode_0] at run
 obtain ⟨a,b,c,d,firstBody,firstOutput,firstRun,firstScope,firstPositive,firstPhysical,firstFunding,firstGlobals,firstDomain,firstEndian,firstCode,firstUpper⟩:=stack_pop_declaration_returned_physical_context s post upper current ancestors layout words valid (ofString "x") (zeroOpcodeAt 1) value code run
 let first:=setVarHOLFinite (ofString "x") (fundingU256 a b c d) {firstBody with locals:=s.locals}
 let firstWords : EvmMemoryOperandWords:={words with stackSize:=words.stackSize-1}
 change evaluateHOLFiniteState first (zeroOpcodeAt 1)=_ at firstRun
 change EvmMemoryOperandAt first current.address firstWords at firstPhysical
 change InterpreterFundingLayout first current.address.toNat upper (current::ancestors) at firstFunding
 change first.code=s.code at firstCode
 change first.memaddrs=s.memaddrs at firstDomain
 have hle : (1#64 : BitVec 64)≤words.stackSize := by
  rw [BitVec.le_def]
  exact Nat.le_trans (by decide) (Nat.succ_le_of_lt firstPositive)
 have decrement : (words.stackSize-1#64).toNat=words.stackSize.toNat-1 := by
  have raw:=BitVec.toNat_sub_of_le hle
  simpa using raw
 have inside : firstWords.stackSize.toNat<firstWords.stackCapacity.toNat := by
  change (words.stackSize-1#64).toNat<words.stackCapacity.toNat
  rw [decrement]
  omega
 have atX : first.locals.lookup (ofString "x")=some (fundingU256 a b c d) := by simp (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_zero_opcode_1] at firstRun
 obtain ⟨third,charged,thirdRun⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned first (ofString "charge_gas") [.const zeroOpcodeFee] v) firstRun
 obtain ⟨enough,thirdPhysical,paid,progress,locals3,globals3,domain3,endian3,installed3,chargeFrame⟩:=charge_gas_discard_normal_physical_context first third upper current ancestors firstFunding firstWords firstPhysical (.const zeroOpcodeFee) zeroOpcodeFee rfl (by decide) (firstCode.trans code) charged
 change EvmMemoryOperandAt third current.address firstWords at thirdPhysical
 rw [source_zero_opcode_2] at thirdRun
 have atX3 : third.locals.lookup (ofString "x")=some (fundingU256 a b c d) := by rw [locals3];exact atX
 have args3 : evalListHOLFinite third (h:=fun x=>Classical.propDecidable (third.memaddrs x)) [.var .local (ofString "x")]=some [fundingU256 a b c d] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atX3]
 have code3 : third.code=originalRuntimeCode:=installed3.trans (firstCode.trans code)
 obtain ⟨word,bodyPost,output,readyRun,scope,bodyMem,bodyGlobals,bodyDomain,bodyEndian,bodyCode⟩:=zero_helper_declaration_returned_word third firstOutput (ofString "r") [.var .local (ofString "x")] (zeroOpcodeAt 3) a b c d value args3 code3 thirdRun
 let ready:=setVarHOLFinite (ofString "r") (.val (.word word)) {bodyPost with locals:=third.locals}
 have readyMemory : ready.memory=bodyPost.memory := rfl
 have readyGlobals : ready.globals=bodyPost.globals := rfl
 have readyDomain : ready.memaddrs=bodyPost.memaddrs := rfl
 have readyEndian : ready.be=bodyPost.be := rfl
 have readyCode : ready.code=bodyPost.code := rfl
 have readyPhysical : EvmMemoryOperandAt ready current.address firstWords:=thirdPhysical.after_context (readyGlobals.trans bodyGlobals) (readyMemory.trans bodyMem) (readyDomain.trans bodyDomain)
 have atR : ready.locals.lookup (ofString "r")=some (.val (.word word)) := by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_zero_opcode_3] at readyRun
 obtain ⟨pushed,pushRun,pushedRun⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned ready (ofString "stack_push_bool") [.var .local (ofString "r")] v) readyRun
 have argsR : evalListHOLFinite ready (h:=fun x=>Classical.propDecidable (ready.memaddrs x)) [.var .local (ofString "r")]=some [.val (.word word)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atR]
 obtain ⟨pushedPhysical,pushedGlobals,pushedLocals,pushedDomain,pushedEndian,pushedInstalled,pushFrame⟩:=stack_push_bool_discard_physical_context ready pushed current.address firstWords readyPhysical (.var .local (ofString "r")) word argsR inside (by intro address below;rw [readyDomain,bodyDomain,domain3,firstDomain];exact fullDomain address below) (readyCode.trans (bodyCode.trans code3)) pushRun
 rw [source_zero_opcode_4] at pushedRun
 rw [source_zero_opcode_5] at pushedRun
 obtain ⟨zeroOut,outputPhysical,outputGlobals,outputDomain,outputEndian,outputInstalled,pcFrame⟩:=pc_add_one_return_physical_context pushed output current.address {firstWords with stackSize:=firstWords.stackSize+1} pushedPhysical value (pushedInstalled.trans (readyCode.trans (bodyCode.trans code3))) pushedRun
 have postMemory : post.memory=output.memory := by rw [firstScope,scope]
 have postGlobals : post.globals=output.globals := by rw [firstScope,scope]
 have postDomain : post.memaddrs=output.memaddrs := by rw [firstScope,scope]
 have postEndian : post.be=output.be := by rw [firstScope,scope]
 have postCode : post.code=output.code := by rw [firstScope,scope]
 have bodyChain : output.memaddrs=bodyPost.memaddrs := outputDomain.trans (pushedDomain.trans readyDomain)
 have finalPhysical : EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)+1} :=
  outputPhysical.after_context postGlobals postMemory postDomain
 have finalDomain : post.memaddrs=third.memaddrs := postDomain.trans (bodyChain.trans bodyDomain)
 have finalFunding : InterpreterFundingLayout post current.address.toNat upper (current.charged zeroOpcodeFee::ancestors) :=
  paid.after_header_frame (upper:=upper) (current:=current.charged zeroOpcodeFee) (ancestors:=ancestors) finalDomain (by
   intro watched above notZero notSixteen
   rw [postMemory]
   exact (pcFrame watched notZero).trans ((pushFrame watched above notSixteen).trans ((congrFun readyMemory watched).trans (congrFun bodyMem watched))))
 refine ⟨zeroOut,enough,finalFunding,progress,finalPhysical,?_,?_,?_,?_,?_⟩
 · exact postGlobals.trans (outputGlobals.trans (pushedGlobals.trans (readyGlobals.trans (bodyGlobals.trans (globals3.trans firstGlobals)))))
 · exact postDomain.trans (bodyChain.trans (bodyDomain.trans (domain3.trans firstDomain)))
 · exact postEndian.trans (outputEndian.trans (pushedEndian.trans (readyEndian.trans (bodyEndian.trans (endian3.trans firstEndian)))))
 · exact postCode.trans (outputInstalled.trans (pushedInstalled.trans (readyCode.trans (bodyCode.trans (installed3.trans firstCode)))))
 · intro watched above notZero notSixteen notLeft notUsed
   rw [postMemory]
   exact (pcFrame watched notZero).trans ((pushFrame watched above notSixteen).trans ((congrFun readyMemory watched).trans ((congrFun bodyMem watched).trans ((chargeFrame watched notLeft notUsed).trans (firstUpper watched notSixteen)))))
#print axioms zero_opcode_body_returned_physical_context
end InitECandidate.Runtime
