import InitECandidate.Runtime.ShiftHelperFrame
import InitECandidate.Runtime.StackPushNoGrowthCallPhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
import InitECandidate.Runtime.ChargeGasPhysicalContext
import InitECandidate.Runtime.InterpreterFundingOffsetFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Real four-limb shift push and PC/return suffix close the next physical
opcode state. -/
theorem shift_push_returned_physical_context {F : Type}
 (kind : ShiftOpcodeKind) (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "r")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (shiftOpcodeAt kind 5)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_shift_opcode_5 kind] at run
 obtain ⟨next,pushed,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "stack_push") [.var .local (ofString "r")] v) run
 obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s next frame words valid [.var .local (ofString "r")] a b c d (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atValue]) inside fullDomain code pushed
 rw [source_shift_opcode_6 kind,source_shift_opcode_7 kind] at tail
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pcFrame⟩:=pc_add_one_return_physical_context next post frame {words with stackSize:=words.stackSize+1} physical value (installed.trans code) tail
 refine ⟨zero,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter
 rw [pcFrame watched notPc]
 exact pushFrame watched above notCounter
#print axioms shift_push_returned_physical_context

/-- The actual `sat_word` amount helper, the shift helper and the four-limb
push/PC suffix close the next physical state. -/
theorem shift_helper_returned_physical_context {F : Type}
 (kind : ShiftOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (a b c d i j k l : BitVec 64) (value : ValueHOL 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atSh : s.locals.lookup (ofString "sh")=some (fundingU256 i j k l))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (shiftOpcodeAt kind 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_shift_opcode_3 kind] at run
 obtain ⟨amount,amountBody,amountOutput,amountTail,amountScope,amountMemory,amountGlobals,amountDomain,amountEndian,amountCode⟩:=shift_amount_declaration_returned_word s post (ofString "n") [.var .local (ofString "sh")] (shiftOpcodeAt kind 4) i j k l value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atSh]) code run
 let readyAmount:=setVarHOLFinite (ofString "n") (.val (.word amount)) {amountBody with locals:=s.locals}
 rw [source_shift_opcode_4 kind] at amountTail
 change readyAmount.memory=s.memory at amountMemory
 change readyAmount.globals=s.globals at amountGlobals
 change readyAmount.memaddrs=s.memaddrs at amountDomain
 change readyAmount.be=s.be at amountEndian
 change readyAmount.code=s.code at amountCode
 have amountKept : readyAmount.memory=s.memory:=amountMemory
 have amountGlobalKept : readyAmount.globals=s.globals:=amountGlobals
 have amountDomainKept : readyAmount.memaddrs=s.memaddrs:=amountDomain
 have amountEndianKept : readyAmount.be=s.be:=amountEndian
 have amountCodeKept : readyAmount.code=s.code:=amountCode
 have physicalAmount : EvmMemoryOperandAt readyAmount frame words:=valid.after_context amountGlobalKept amountKept amountDomainKept
 have atXr : readyAmount.locals.lookup (ofString "x")=some (fundingU256 a b c d) := by
  simp (config:={decide:=true}) [readyAmount,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atX]
 have atNr : readyAmount.locals.lookup (ofString "n")=some (.val (.word amount)) := by simp [readyAmount,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨r0,r1,r2,r3,body,output,tail,scope,memory,globals,domain,endian,installed⟩:=shift_helper_declaration_returned_frame kind readyAmount amountOutput (ofString "r") [.var .local (ofString "x"),.var .local (ofString "n")] (shiftOpcodeAt kind 5) a b c d amount value (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atXr,atNr]) (amountCodeKept.trans code) amountTail
 let ready:=setVarHOLFinite (ofString "r") (fundingU256 r0 r1 r2 r3) {body with locals:=readyAmount.locals}
 change evaluateHOLFiniteState ready (shiftOpcodeAt kind 5)=(some (.returned value),output) at tail
 change ready.memory=readyAmount.memory at memory
 change ready.globals=readyAmount.globals at globals
 change ready.memaddrs=readyAmount.memaddrs at domain
 change ready.be=readyAmount.be at endian
 change ready.code=readyAmount.code at installed
 have readyMemory : ready.memory=s.memory:=memory.trans amountKept
 have readyGlobals : ready.globals=s.globals:=globals.trans amountGlobalKept
 have readyDomain : ready.memaddrs=s.memaddrs:=domain.trans amountDomainKept
 have readyEndian : ready.be=s.be:=endian.trans amountEndianKept
 have readyCode : ready.code=s.code:=installed.trans amountCodeKept
 have physical : EvmMemoryOperandAt ready frame words:=physicalAmount.after_context globals memory domain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=shift_push_returned_physical_context kind ready output frame words physical r0 r1 r2 r3 value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [amountScope,scope]) (by rw [amountScope,scope]) (by rw [amountScope,scope]),?_,?_,?_,?_,?_⟩
 · rw [amountScope,scope];exact finalGlobals.trans readyGlobals
 · rw [amountScope,scope];exact finalDomain.trans readyDomain
 · rw [amountScope,scope];exact finalEndian.trans readyEndian
 · rw [amountScope,scope];exact finalCode.trans readyCode
 · intro watched above notPc notCounter
   rw [amountScope,scope,upperFrame watched above notPc notCounter,readyMemory]

#print axioms shift_helper_returned_physical_context

/-- Actual shift charge and helper/push/PC suffix: next concrete operand state
plus strictly funded progress. -/
theorem shift_charged_returned_physical_context
 (kind : ShiftOpcodeKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (a b c d i j k l : BitVec 64) (value : ValueHOL 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atSh : s.locals.lookup (ofString "sh")=some (fundingU256 i j k l))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (shiftOpcodeAt kind 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧shiftOpcodeFee kind≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged (shiftOpcodeFee kind)::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged (shiftOpcodeFee kind)::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→post.memory watched=s.memory watched) := by
 rw [source_shift_opcode_2 kind] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_gas") [.const (shiftOpcodeFee kind)] v) run
 obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,chargeFrame⟩:=charge_gas_discard_normal_physical_context s next upper current ancestors layout words valid (.const (shiftOpcodeFee kind)) (shiftOpcodeFee kind) rfl (by cases kind <;>decide) code charged
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,tailFrame⟩:=shift_helper_returned_physical_context kind next post current.address words physical a b c d i j k l value (by rw [locals];exact atX) (by rw [locals];exact atSh) inside (by intro address below;rw [domain];exact fullDomain address below) (installed.trans code) tail
 have finalFunding:=InterpreterFundingLayout.after_header_frame (upper:=upper) (current:=current.charged (shiftOpcodeFee kind)) (ancestors:=ancestors) paid finalDomain (fun watched above notPc notCounter => tailFrame watched (by simpa [InterpreterFundingFrame.charged] using above) (by simpa [InterpreterFundingFrame.charged] using notPc) (by simpa [InterpreterFundingFrame.charged] using notCounter))
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter notLeft notUsed
 rw [tailFrame watched above notPc notCounter]
 exact chargeFrame watched notLeft notUsed
#print axioms shift_charged_returned_physical_context
end InitECandidate.Runtime

