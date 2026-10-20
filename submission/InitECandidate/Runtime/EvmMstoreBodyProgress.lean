import InitECandidate.Runtime.EvmMstoreChargedTail
import InitECandidate.Runtime.InterpreterFundingStackPop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- Entire original MSTORE: both checked real pops, literal charge, saturation,
32-32-byte writerr and PC advance. Every successful body return strictly increases the
actual accumulated used gas while retaining all live funding records. -/
theorem mstore_body_returned_progress
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (base length capacity pointer scratch pc index : BitVec 64) (value : ValueHOL 64)
 (currentAligned : length.toNat%32=0)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (headerDomain : ∀offset∈([0,16,24,32,40] : List (BitVec 64)),s.memaddrs (current.address+offset))
 (baseAt : s.memory (current.address+24)=.word base)
 (lengthAt : s.memory (current.address+32)=.word length)
 (capacityAt : s.memory (current.address+40)=.word capacity)
 (pcAt : s.memory (current.address+0)=.word pc)
 (indexAt : s.memory (current.address+16)=.word index)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (lengthOrder : length.toNat≤capacity.toNat)
 (oldExtent : base.toNat+capacity.toNat≤pointer.toNat)
 (ordered : pointer.toNat≤scratch.toNat)
 (belowFrame : scratch.toNat≤current.address.toNat)
 (frameExtent : current.address.toNat+280≤33806089496)
 (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_op_mstore)=(some (.returned value),post)) :
 value=.val (.word 0) ∧∃total : BitVec 64,3≤total.toNat ∧total≤current.gas.left ∧
 InterpreterFundingLayout post current.address.toNat upper (current.charged total::ancestors) ∧
 interpreterFundingUsed (current::ancestors) < interpreterFundingUsed (current.charged total::ancestors) := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (mstoreAt 0)=_ at run
 rw [source_mstore_0] at run
 obtain ⟨sa,sb,sc,sd,firstBody,firstOutput,firstRun,firstScope,firstPositive,firstMemory,firstGlobals,firstClock,firstDomain,firstEndian,firstCode⟩:=stack_pop_declaration_returned_frame s post (ofString "start") (mstoreAt 1) current.address index value atFrame (headerDomain 16 (by simp)) indexAt code run
 let first:=setVarHOLFinite (ofString "start") (fundingU256 sa sb sc sd) {firstBody with locals:=s.locals}
 change evaluateHOLFiniteState first (mstoreAt 1)=_ at firstRun
 have firstLayout : InterpreterFundingLayout first current.address.toNat upper (current::ancestors):=interpreter_funding_after_stack_counter s first upper current ancestors layout (index-1) firstMemory firstDomain
 have firstIndex : first.memory (current.address+16)=.word (index-1) := by change firstBody.memory _=_;rw [firstMemory];simp [sourceWriteWord]
 rw [source_mstore_1] at firstRun
 obtain ⟨a,b,c,d,secondBody,secondOutput,secondRun,secondScope,secondPositive,secondMemory,secondGlobals,secondClock,secondDomain,secondEndian,secondCode⟩:=stack_pop_declaration_returned_frame first firstOutput (ofString "value") (mstoreAt 2) current.address (index-1) value (by change firstBody.globals.lookup _=_;rw [firstGlobals];exact atFrame) (by change firstBody.memaddrs _;rw [firstDomain];exact headerDomain 16 (by simp)) firstIndex (firstCode.trans code) firstRun
 let second:=setVarHOLFinite (ofString "value") (fundingU256 a b c d) {secondBody with locals:=first.locals}
 change evaluateHOLFiniteState second (mstoreAt 2)=_ at secondRun
 have secondLayout : InterpreterFundingLayout second current.address.toNat upper (current::ancestors):=interpreter_funding_after_stack_counter first second upper current ancestors firstLayout ((index-1)-1) secondMemory secondDomain
 have globals : second.globals=s.globals:=secondGlobals.trans firstGlobals
 have domains : second.memaddrs=s.memaddrs:=secondDomain.trans firstDomain
 have memory (offset : BitVec 64) (different : offset≠16#64) : second.memory (current.address+offset)=s.memory (current.address+offset) := by
  have separate : current.address+offset≠current.address+16#64 := by intro eq;apply different;exact add_left_cancel eq
  change secondBody.memory _=_
  rw [secondMemory]
  change (if current.address+offset=current.address+16#64 then _ else _)=_
  rw [if_neg separate]
  change firstBody.memory _=_
  rw [firstMemory]
  change (if current.address+offset=current.address+16#64 then _ else _)=_
  rw [if_neg separate]
 obtain ⟨zero,total,baseBound,enough,paid,progress⟩:=mstore_charged_tail_returned_progress second secondOutput upper current ancestors secondLayout base length capacity pointer scratch pc sa sb sc sd a b c d value currentAligned (by rw [globals];exact atFrame) (by intro offset member;rw [domains];exact headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)) (by rw [memory 24 (by decide)];exact baseAt) (by rw [memory 32 (by decide)];exact lengthAt) (by rw [memory 40 (by decide)];exact capacityAt) (by rw [memory 0 (by decide)];exact pcAt) (by rw [globals];exact atPointer) (by rw [globals];exact atScratch) lengthOrder oldExtent ordered belowFrame frameExtent (by simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by simp [second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (secondCode.trans (firstCode.trans code)) (by rw [domains];exact domOK) secondRun
 refine ⟨zero,total,baseBound,enough,?_,progress⟩
 apply paid.after_memory
 · rw [firstScope,secondScope]
 · rw [firstScope,secondScope]
#print axioms mstore_body_returned_progress
end InitECandidate.Runtime
