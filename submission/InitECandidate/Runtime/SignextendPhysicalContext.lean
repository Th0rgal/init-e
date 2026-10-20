import InitECandidate.Runtime.SignextendOpcodeSource
import InitECandidate.Runtime.SignextendHelperFrame
import InitECandidate.Runtime.StackPushNoGrowthCallPhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
import InitECandidate.Runtime.ChargeGasPhysicalContext
import InitECandidate.Runtime.InterpreterFundingOffsetFrame
import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Real four-limb sign-extension push and PC/return suffix. -/
theorem signextend_push_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "r")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (signextendOpcodeAt 5)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_signextend_opcode_5] at run
 obtain ⟨next,pushed,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "stack_push") [.var .local (ofString "r")] v) run
 obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s next frame words valid [.var .local (ofString "r")] a b c d (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atValue]) inside fullDomain code pushed
 rw [source_signextend_opcode_6,source_signextend_opcode_7] at tail
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pcFrame⟩:=pc_add_one_return_physical_context next post frame {words with stackSize:=words.stackSize+1} physical value (installed.trans code) tail
 refine ⟨zero,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter
 rw [pcFrame watched notPc]
 exact pushFrame watched above notCounter
#print axioms signextend_push_returned_physical_context

/-- The actual `sat_word` byte-width helper, the sign-extension helper and the
four-limb push/PC suffix close the next physical state. -/
theorem signextend_helper_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (a b c d i j k l : BitVec 64) (value : ValueHOL 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atB : s.locals.lookup (ofString "b")=some (fundingU256 i j k l))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (signextendOpcodeAt 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_signextend_opcode_3] at run
 obtain ⟨width,widthBody,widthOutput,widthTail,widthScope,widthMemory,widthGlobals,widthDomain,widthEndian,widthCode⟩:=shift_amount_declaration_returned_word s post (ofString "bw") [.var .local (ofString "b")] (signextendOpcodeAt 4) i j k l value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atB]) code run
 let readyWidth:=setVarHOLFinite (ofString "bw") (.val (.word width)) {widthBody with locals:=s.locals}
 rw [source_signextend_opcode_4] at widthTail
 change readyWidth.memory=s.memory at widthMemory
 change readyWidth.globals=s.globals at widthGlobals
 change readyWidth.memaddrs=s.memaddrs at widthDomain
 change readyWidth.be=s.be at widthEndian
 change readyWidth.code=s.code at widthCode
 have widthKept : readyWidth.memory=s.memory:=widthMemory
 have widthGlobalKept : readyWidth.globals=s.globals:=widthGlobals
 have widthDomainKept : readyWidth.memaddrs=s.memaddrs:=widthDomain
 have widthEndianKept : readyWidth.be=s.be:=widthEndian
 have widthCodeKept : readyWidth.code=s.code:=widthCode
 have physicalWidth : EvmMemoryOperandAt readyWidth frame words:=valid.after_context widthGlobalKept widthKept widthDomainKept
 have atXr : readyWidth.locals.lookup (ofString "x")=some (fundingU256 a b c d) := by
  simp (config:={decide:=true}) [readyWidth,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atX]
 have atBwr : readyWidth.locals.lookup (ofString "bw")=some (.val (.word width)) := by simp [readyWidth,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨r0,r1,r2,r3,body,output,tail,scope,memory,globals,domain,endian,installed⟩:=signextend_helper_declaration_returned_frame readyWidth widthOutput (ofString "r") [.var .local (ofString "bw"),.var .local (ofString "x")] (signextendOpcodeAt 5) width a b c d value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atBwr,atXr]) (widthCodeKept.trans code) widthTail
 let ready:=setVarHOLFinite (ofString "r") (fundingU256 r0 r1 r2 r3) {body with locals:=readyWidth.locals}
 change evaluateHOLFiniteState ready (signextendOpcodeAt 5)=(some (.returned value),output) at tail
 change ready.memory=readyWidth.memory at memory
 change ready.globals=readyWidth.globals at globals
 change ready.memaddrs=readyWidth.memaddrs at domain
 change ready.be=readyWidth.be at endian
 change ready.code=readyWidth.code at installed
 have readyMemory : ready.memory=s.memory:=memory.trans widthKept
 have readyGlobals : ready.globals=s.globals:=globals.trans widthGlobalKept
 have readyDomain : ready.memaddrs=s.memaddrs:=domain.trans widthDomainKept
 have readyEndian : ready.be=s.be:=endian.trans widthEndianKept
 have readyCode : ready.code=s.code:=installed.trans widthCodeKept
 have physical : EvmMemoryOperandAt ready frame words:=physicalWidth.after_context globals memory domain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=signextend_push_returned_physical_context ready output frame words physical r0 r1 r2 r3 value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [widthScope,scope]) (by rw [widthScope,scope]) (by rw [widthScope,scope]),?_,?_,?_,?_,?_⟩
 · rw [widthScope,scope];exact finalGlobals.trans readyGlobals
 · rw [widthScope,scope];exact finalDomain.trans readyDomain
 · rw [widthScope,scope];exact finalEndian.trans readyEndian
 · rw [widthScope,scope];exact finalCode.trans readyCode
 · intro watched above notPc notCounter
   rw [widthScope,scope,upperFrame watched above notPc notCounter,readyMemory]
#print axioms signextend_helper_returned_physical_context

/-- Actual sign-extension charge and helper/push/PC suffix. -/
theorem signextend_charged_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (a b c d i j k l : BitVec 64) (value : ValueHOL 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atB : s.locals.lookup (ofString "b")=some (fundingU256 i j k l))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (signextendOpcodeAt 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧signextendOpcodeFee≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged signextendOpcodeFee::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged signextendOpcodeFee::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_signextend_opcode_2] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_gas") [.const signextendOpcodeFee] v) run
 obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,chargeFrame⟩:=charge_gas_discard_normal_physical_context s next upper current ancestors layout words valid (.const signextendOpcodeFee) signextendOpcodeFee rfl (by decide) code charged
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,tailFrame⟩:=signextend_helper_returned_physical_context next post current.address words physical a b c d i j k l value (by rw [locals];exact atX) (by rw [locals];exact atB) inside (by intro address below;rw [domain];exact fullDomain address below) (installed.trans code) tail
 have finalFunding:=InterpreterFundingLayout.after_header_frame (upper:=upper) (current:=current.charged signextendOpcodeFee) (ancestors:=ancestors) paid finalDomain (fun watched above notPc notCounter => tailFrame watched (by simpa [InterpreterFundingFrame.charged] using above) (by simpa [InterpreterFundingFrame.charged] using notPc) (by simpa [InterpreterFundingFrame.charged] using notCounter))
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter notLeft notUsed
 rw [tailFrame watched above notPc notCounter]
 exact chargeFrame watched notLeft notUsed
#print axioms signextend_charged_returned_physical_context

/-- Actual complete original op_signextend body. -/
theorem signextend_opcode_body_returned_physical_context
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (value : ValueHOL 64)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s signextendOpcodeBody=(some (.returned value),post)) :
 value=.val (.word 0) ∧signextendOpcodeFee≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged signextendOpcodeFee::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged signextendOpcodeFee::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_signextend_opcode_body,source_signextend_opcode_0] at run
 obtain ⟨a,b,c,d,firstBody,firstOutput,firstRun,firstScope,firstPositive,firstPhysical,firstFunding,firstGlobals,firstDomain,firstEndian,firstCode,firstUpper⟩:=stack_pop_declaration_returned_physical_context s post upper current ancestors layout words valid (ofString "b") (signextendOpcodeAt 1) value code run
 let first:=setVarHOLFinite (ofString "b") (fundingU256 a b c d) {firstBody with locals:=s.locals}
 let firstWords : EvmMemoryOperandWords:={words with stackSize:=words.stackSize-1}
 change evaluateHOLFiniteState first (signextendOpcodeAt 1)=_ at firstRun
 change EvmMemoryOperandAt first current.address firstWords at firstPhysical
 change InterpreterFundingLayout first current.address.toNat upper (current::ancestors) at firstFunding
 change first.code=s.code at firstCode
 change first.memaddrs=s.memaddrs at firstDomain
 rw [source_signextend_opcode_1] at firstRun
 obtain ⟨e,f,g,h,secondBody,secondOutput,secondRun,secondScope,secondPositive,secondPhysical,secondFunding,secondGlobals,secondDomain,secondEndian,secondCode,secondUpper⟩:=stack_pop_declaration_returned_physical_context first firstOutput upper current ancestors firstFunding firstWords firstPhysical (ofString "x") (signextendOpcodeAt 2) value (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "x") (fundingU256 e f g h) {secondBody with locals:=first.locals}
 let secondWords : EvmMemoryOperandWords:={firstWords with stackSize:=firstWords.stackSize-1}
 change evaluateHOLFiniteState second (signextendOpcodeAt 2)=_ at secondRun
 change EvmMemoryOperandAt second current.address secondWords at secondPhysical
 change InterpreterFundingLayout second current.address.toNat upper (current::ancestors) at secondFunding
 change second.code=first.code at secondCode
 change second.memaddrs=first.memaddrs at secondDomain
 have atB : second.locals.lookup (ofString "b")=some (fundingU256 a b c d) := by simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atX : second.locals.lookup (ofString "x")=some (fundingU256 e f g h) := by simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have decrement : (firstWords.stackSize-1#64).toNat=firstWords.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤firstWords.stackSize.toNat;change 1≤firstWords.stackSize.toNat;omega))
 have inside : secondWords.stackSize.toNat<secondWords.stackCapacity.toNat := by
  change (firstWords.stackSize-1#64).toNat<firstWords.stackCapacity.toNat
  rw [decrement]
  have previous:=firstPhysical.stackSizeBound
  omega
 obtain ⟨zero,enough,paid,progress,physical,globals,domain,endian,installed,upperFrame⟩:=signextend_charged_returned_physical_context second secondOutput upper current ancestors secondFunding secondWords secondPhysical e f g h a b c d value atX atB inside (by intro address below;rw [secondDomain,firstDomain];exact fullDomain address below) (secondCode.trans (firstCode.trans code)) secondRun
 have finalPhysical : EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=(words.stackSize-1)-1+1} := by
  apply EvmMemoryOperandAt.after_context (post:=post) physical
  · rw [firstScope,secondScope]
  · rw [firstScope,secondScope]
  · rw [firstScope,secondScope]
 have finalFunding : InterpreterFundingLayout post current.address.toNat upper (current.charged signextendOpcodeFee::ancestors):=
  paid.after_memory (by rw [firstScope,secondScope]) (by rw [firstScope,secondScope])
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,?_,?_,?_,?_,?_⟩
 · rw [firstScope,secondScope];exact globals.trans (secondGlobals.trans firstGlobals)
 · rw [firstScope,secondScope,domain,secondDomain,firstDomain]
 · rw [firstScope,secondScope];exact endian.trans (secondEndian.trans firstEndian)
 · rw [firstScope,secondScope];exact installed.trans (secondCode.trans firstCode)
 · intro watched above notPc notCounter notLeft notUsed
   rw [firstScope,secondScope,upperFrame watched above notPc notCounter notLeft notUsed,secondUpper watched notCounter,firstUpper watched notCounter]
#print axioms signextend_opcode_body_returned_physical_context
end InitECandidate.Runtime

