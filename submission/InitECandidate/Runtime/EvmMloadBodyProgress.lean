import InitECandidate.Runtime.EvmMloadChargedTail
import InitECandidate.Runtime.InterpreterFundingStackPop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Whole original MLOAD, deriving actual pop/read/push values and strict actual
gas progress with concrete owned operand/vector buffers, not callee callbacks. -/
theorem mload_body_returned_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base index capacity scratch pointer pc memoryBase memoryLength memoryCapacity : BitVec 64) (value : ValueHOL 64)
 (currentAligned : memoryLength.toNat%32=0)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([0,8,16,24,32,40,232] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+8)=.word base)
 (indexAt : s.memory (current.address+16)=.word index)
 (capacityAt : s.memory (current.address+232)=.word capacity)
 (memoryAt : s.memory (current.address+24)=.word memoryBase)
 (lengthAt : s.memory (current.address+32)=.word memoryLength)
 (memoryCapacityAt : s.memory (current.address+40)=.word memoryCapacity)
 (pcAt : s.memory (current.address+0)=.word pc)
 (positive : 1≤capacity.toNat) (capacityBound : capacity.toNat≤1024) (indexBound : index.toNat≤capacity.toNat)
 (bufferExtent : base.toNat+capacity.toNat*32≤current.address.toNat)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : memoryLength.toNat≤memoryCapacity.toNat)
 (oldExtent : memoryBase.toNat+memoryCapacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat) (belowFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_op_mload)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃total : BitVec 64,3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (mloadAt 0)=_ at run
 rw [source_mload_0] at run
 obtain ⟨sa,sb,sc,sd,body,output,tail,scope,popPositive,memory,globals,clock,domain,endian,installed⟩:=stack_pop_declaration_returned_frame s post (ofString "start") (mloadAt 1) current.address index value atFrame (headerDomain 16 (by simp)) indexAt code run
 let ready:=setVarHOLFinite (ofString "start") (fundingU256 sa sb sc sd) {body with locals:=s.locals}
 change evaluateHOLFiniteState ready (mloadAt 1)=_ at tail
 have readyGlobals : ready.globals=s.globals:=globals
 have readyDomain : ready.memaddrs=s.memaddrs:=domain
 have valid : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=interpreter_funding_after_stack_counter s ready upper current ancestors layout (index-1) memory domain
 have readIndex : ready.memory (current.address+16)=.word (index-1) := by change body.memory _=_;rw [memory];simp [sourceWriteWord]
 have keep (offset : BitVec 64) (different : offset≠16#64) : ready.memory (current.address+offset)=s.memory (current.address+offset) := by
  change body.memory _=_
  rw [memory]
  change (if current.address+offset=current.address+16#64 then _ else _)=_
  have separate : current.address+offset≠current.address+16#64 := by intro eq;exact different (add_left_cancel eq)
  rw [if_neg separate]
 have decrement : (index-1#64).toNat=index.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤ index.toNat;change 1≤ index.toNat;omega))
 obtain ⟨zero,total,baseBound,enough,paid,progress⟩:=mload_charged_tail_returned_progress ready output upper current ancestors valid base (index-1) capacity scratch pointer pc memoryBase memoryLength memoryCapacity sa sb sc sd value currentAligned (by rw [readyGlobals];exact atFrame) (by intro offset member;rw [readyDomain];exact headerDomain offset member) ((keep 8 (by decide)).trans baseAt) readIndex ((keep 232 (by decide)).trans capacityAt) ((keep 24 (by decide)).trans memoryAt) ((keep 32 (by decide)).trans lengthAt) ((keep 40 (by decide)).trans memoryCapacityAt) ((keep 0 (by decide)).trans pcAt) positive capacityBound (by change (index-1#64).toNat≤capacity.toNat;rw [decrement];omega) bufferExtent (by rw [readyGlobals];exact atPointer) (by rw [readyGlobals];exact atScratch) lengthOrder oldExtent ordered belowFrame frameExtent (by intro address below;rw [readyDomain];exact fullDomain address below) (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (installed.trans code) tail
 exact ⟨zero,total,baseBound,enough,paid.after_memory (by rw [scope]) (by rw [scope]),progress⟩
#print axioms mload_body_returned_progress
end InitECandidate.Runtime
