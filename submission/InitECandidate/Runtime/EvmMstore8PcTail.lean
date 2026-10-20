import InitECandidate.Runtime.EvmMstore8WriteFrame
import InitECandidate.Runtime.PcAddCall
import InitECandidate.Runtime.VmFn_pc_add
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Real final pc_add and return of MSTORE8 keep all live regular funding. -/
theorem mstore8_pc_tail_returned_funding {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (pc : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (domain : s.memaddrs (current.address+0))
 (pcAt : s.memory (current.address+0)=.word pc)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (mstore8At 5)=(some (.returned value),post)) :
 value=.val (.word 0) ∧InterpreterFundingLayout post current.address.toNat upper (current::ancestors) ∧
 post.memory=(sourceWriteWord s (current.address+0) (pc+1)).memory ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [source_mstore8_5] at run
 have clock:=call_seq_returned_clock run
 have installed : s.code.lookup (ofString "pc_add")=some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one) := by rw [code];exact vmLookup_pc_add
 have called:=evaluate_pcAdd_call s (.const 1) current.address pc 1 (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) installed clock atFrame domain pcAt
 rw [evaluateHOLFiniteState_seq_line780,called] at run
 change evaluateHOLFiniteState (pcAddCallPost s current.address pc 1) (mstore8At 6)=_ at run
 rw [source_mstore8_6,evaluateHOLFiniteState_return] at run
 simp only [evalHOLExact] at run
 simp only [shapeOfHOLExact,shapeEqHOL] at run
 have equal : value=.val (.word 0) ∧post=emptyLocalsHOLFinite (pcAddCallPost s current.address pc 1) := by
  split at run
  · exact ⟨by simpa using (Prod.mk.inj run).1.symm,(Prod.mk.inj run).2.symm⟩
  · simp at run
 rcases equal with ⟨rfl,rfl⟩
 refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl⟩
 constructor
 · exact layout.upperBound
 · intro record member
   have metadata:=layout.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=emptyLocalsHOLFinite (pcAddCallPost s current.address pc 1)) metadata rfl
   intro offset included
   have positive : 0<offset.toNat ∧offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural record upper metadata.extent layout.upperBound offset positive.2
   have different : record.address+offset≠current.address+0#64 := by
    intro eq
    have same:=congrArg BitVec.toNat eq
    simp only [BitVec.add_zero] at same
    rw [natural] at same
    have lower:=metadata.lowerBound
    omega
   change (if record.address+offset=current.address+0#64 then _ else _)=_
   rw [if_neg different]
 · exact layout.disjoint
 · exact layout.budget
#print axioms mstore8_pc_tail_returned_funding
end InitECandidate.Runtime
