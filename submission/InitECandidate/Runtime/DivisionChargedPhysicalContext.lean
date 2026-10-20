import InitECandidate.Runtime.DivisionHelperDeclaration
import InitECandidate.Runtime.StackPushNoGrowthCallPhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
import InitECandidate.Runtime.ChargeGasPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The operand assertion depends on memory only at the seven header words, so a
step that preserves exactly those words re-establishes it. -/
theorem EvmMemoryOperandAt.after_context_words {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {frame : BitVec 64} {words : EvmMemoryOperandWords}
 (valid : EvmMemoryOperandAt s frame words)
 (globals : post.globals=s.globals)
 (memory : ∀offset,offset∈([0,8,16,24,32,40,232] : List (BitVec 64))→post.memory (frame+offset)=s.memory (frame+offset))
 (domain : post.memaddrs=s.memaddrs) : EvmMemoryOperandAt post frame words := by
 constructor
 · rw [globals];exact valid.ev
 · rw [globals];exact valid.framePointer
 · rw [globals];exact valid.scratchPointer
 · intro offset member;rw [domain];exact valid.headerDomain offset member
 · rw [memory 0 (by decide)];exact valid.pc
 · rw [memory 8 (by decide)];exact valid.stackBase
 · rw [memory 16 (by decide)];exact valid.stackSize
 · rw [memory 232 (by decide)];exact valid.stackCapacity
 · rw [memory 24 (by decide)];exact valid.memoryBase
 · rw [memory 32 (by decide)];exact valid.memoryLength
 · rw [memory 40 (by decide)];exact valid.memoryCapacity
 · exact valid.stackCapacityPositive
 · exact valid.stackCapacityBound
 · exact valid.stackSizeBound
 · exact valid.stackLower
 · exact valid.stackExtent
 · exact valid.memoryAligned
 · exact valid.memoryLengthBound
 · exact valid.memoryExtent
 · exact valid.pointers
 · exact valid.frameExtent
#print axioms EvmMemoryOperandAt.after_context_words

/-- Real four-limb division push and PC/return suffix close the next physical
opcode state. -/
theorem division_push_returned_physical_context {F : Type}
 (kind : DivisionOpcodeKind) (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "r")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (divisionOpcodeAt kind 4)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_division_opcode_4 kind] at run
 obtain ⟨next,pushed,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "stack_push") [.var .local (ofString "r")] v) run
 obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s next frame words valid [.var .local (ofString "r")] a b c d (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atValue]) inside fullDomain code pushed
 rw [source_division_opcode_5 kind,source_division_opcode_6 kind] at tail
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,pcFrame⟩:=pc_add_one_return_physical_context next post frame {words with stackSize:=words.stackSize+1} physical value (installed.trans code) tail
 refine ⟨zero,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter
 rw [pcFrame watched notPc]
 exact pushFrame watched above notCounter
#print axioms division_push_returned_physical_context

/-- The actual division helper declaration (workspace window) and the four-limb
push/PC suffix close the next physical state, with memory preserved outside the
`u256_ws` window as well as at the frame's own header words. -/
theorem division_helper_returned_physical_context {F : Type}
 (kind : DivisionOpcodeKind) (s post : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords)
 (valid : EvmMemoryOperandAt s frame words)
 (a b c d e f g h : BitVec 64) (value : ValueHOL 64) (U : BitVec 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atY : s.locals.lookup (ofString "y")=some (fundingU256 e f g h))
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (domOK : DomOK s.memaddrs) (hU : U.toNat+640≤2^64)
 (headerOutside : ∀offset,offset∈([0,8,16,24,32,40,232] : List (BitVec 64))→¬ WS U (frame+offset))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (divisionOpcodeAt kind 3)=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+0→watched≠frame+16→¬ WS U watched→post.memory watched=s.memory watched) := by
 rw [source_division_opcode_3 kind] at run
 obtain ⟨r0,r1,r2,r3,body,output,tail,scope,memory,globals,domain,endian,installed⟩:=division_helper_declaration_returned_frame kind s post (ofString "r")
  [.var .local (ofString "x"),.var .local (ofString "y")] (divisionOpcodeAt kind 4) a b c d e f g h value U
  (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atX,atY]) code ws domOK hU run
 let ready:=setVarHOLFinite (ofString "r") (fundingU256 r0 r1 r2 r3) {body with locals:=s.locals}
 have readyMemory : ∀watched : BitVec 64, ¬ WS U watched → ready.memory watched = s.memory watched := by
  intro watched hw
  exact memory watched hw
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have readyEndian : ready.be=s.be:=endian
 have readyCode : ready.code=s.code:=installed
 have physical : EvmMemoryOperandAt ready frame words:=valid.after_context_words readyGlobals
  (fun offset member => readyMemory (frame+offset) (headerOutside offset member)) readyDomain
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,upperFrame⟩:=division_push_returned_physical_context kind ready output frame words physical r0 r1 r2 r3 value (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) inside (by intro address below;rw [readyDomain];exact fullDomain address below) (readyCode.trans code) tail
 refine ⟨zero,finalPhysical.after_context (by rw [scope]) (by rw [scope]) (by rw [scope]),?_,?_,?_,?_,?_⟩
 · rw [scope,finalGlobals,readyGlobals]
 · rw [scope,finalDomain,readyDomain]
 · rw [scope,finalEndian];exact endian
 · rw [scope,finalCode,readyCode]
 · intro watched above notPc notCounter hw
   rw [scope,upperFrame watched above notPc notCounter,readyMemory watched hw]

/-- Funding survives a step that keeps the domain and preserves memory above the
frame outside a window disjoint from every funding word of the chain (plus the
frame's own two header words). This is the division-specific analogue of
`after_header_frame`. -/
theorem InterpreterFundingLayout.after_window_frame_full {F : Type}
 {s post : PanSemStateFiniteExact 64 F}
 {upper : Nat} {current : InterpreterFundingFrame} {ancestors : List InterpreterFundingFrame}
 (valid : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (domain : post.memaddrs=s.memaddrs)
 (window : BitVec 64)
 (outside : ∀record,record∈(current::ancestors)→∀offset,offset∈interpreterFundingOffsets→¬ WS window (record.address+offset))
 (memory : ∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→¬ WS window watched→post.memory watched=s.memory watched) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 have currentAt:=valid.records current (by simp)
 have zeroNatural:=interpreter_funding_offset_natural current upper currentAt.extent valid.upperBound (0#64) (by decide)
 have leftNatural:=interpreter_funding_offset_natural current upper currentAt.extent valid.upperBound (16#64) (by decide)
 constructor
 · exact valid.upperBound
 · intro record member
   have old:=valid.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=post) old domain
   intro offset included
   have offsetBounds : 64≤offset.toNat ∧offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural record upper old.extent valid.upperBound offset offsetBounds.2
   apply memory (record.address+offset) (by rw [natural];have bound:=old.lowerBound;omega)
   · intro equal
     have same:=congrArg BitVec.toNat equal
     change (record.address+offset).toNat=(current.address+0#64).toNat at same
     rw [BitVec.add_zero,natural] at same
     have bound:=old.lowerBound
     omega
   · intro equal
     have same:=congrArg BitVec.toNat equal
     change (record.address+offset).toNat=(current.address+16#64).toNat at same
     rw [natural,leftNatural] at same
     change record.address.toNat+offset.toNat=current.address.toNat+16 at same
     have bound:=old.lowerBound
     omega
   · exact outside record member offset included
 · exact valid.disjoint
 · exact valid.budget
#print axioms InterpreterFundingLayout.after_window_frame_full

/-- Actual division charge and helper/push/PC suffix: next concrete operand
state plus strictly funded progress, carrying the explicit workspace-window
disjointness for the header words and the funding chain. -/
theorem division_charged_returned_physical_context
 (kind : DivisionOpcodeKind) (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (a b c d e f g h : BitVec 64) (value : ValueHOL 64) (U : BitVec 64)
 (atX : s.locals.lookup (ofString "x")=some (fundingU256 a b c d))
 (atY : s.locals.lookup (ofString "y")=some (fundingU256 e f g h))
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (domOK : DomOK s.memaddrs) (hU : U.toNat+640≤2^64)
 (headerOutside : ∀offset,offset∈([0,8,16,24,32,40,232] : List (BitVec 64))→¬ WS U (current.address+offset))
 (chainOutside : ∀record,record∈(current.charged (divisionOpcodeFee kind)::ancestors)→∀offset,offset∈interpreterFundingOffsets→¬ WS U (record.address+offset))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (divisionOpcodeAt kind 2)=(some (.returned value),post)) :
 value=.val (.word 0) ∧divisionOpcodeFee kind≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged (divisionOpcodeFee kind)::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged (divisionOpcodeFee kind)::ancestors) ∧
 EvmMemoryOperandAt post current.address {words with pc:=words.pc+1,stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→watched≠current.address+64→watched≠current.address+184→¬ WS U watched→post.memory watched=s.memory watched) := by
 rw [source_division_opcode_2 kind] at run
 obtain ⟨next,charged,tail⟩:=seq_returned_of_nonreturning_first (fun v=>discard_call_not_returned s (ofString "charge_gas") [.const (divisionOpcodeFee kind)] v) run
 obtain ⟨enough,physical,paid,progress,locals,globals,domain,endian,installed,chargeFrame⟩:=charge_gas_discard_normal_physical_context s next upper current ancestors layout words valid (.const (divisionOpcodeFee kind)) (divisionOpcodeFee kind) rfl (by cases kind <;>decide) code charged
 obtain ⟨zero,finalPhysical,finalGlobals,finalDomain,finalEndian,finalCode,tailFrame⟩:=division_helper_returned_physical_context kind next post current.address words physical a b c d e f g h value U (by rw [locals];exact atX) (by rw [locals];exact atY) (by rw [globals];exact ws) (by rw [domain];exact domOK) hU headerOutside inside (by intro address below;rw [domain];exact fullDomain address below) (installed.trans code) tail
 have finalFunding:=paid.after_window_frame_full (upper:=upper) (current:=current.charged (divisionOpcodeFee kind)) (ancestors:=ancestors) finalDomain U chainOutside (fun watched above notPc notCounter hw => tailFrame watched (by simpa [InterpreterFundingFrame.charged] using above) (by simpa [InterpreterFundingFrame.charged] using notPc) (by simpa [InterpreterFundingFrame.charged] using notCounter) hw)
 refine ⟨zero,enough,finalFunding,progress,finalPhysical,finalGlobals.trans globals,finalDomain.trans domain,finalEndian.trans endian,finalCode.trans installed,?_⟩
 intro watched above notPc notCounter notLeft notUsed hw
 rw [tailFrame watched above notPc notCounter hw]
 exact chargeFrame watched notLeft notUsed
#print axioms division_charged_returned_physical_context
end InitECandidate.Runtime
