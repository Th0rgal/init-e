import InitECandidate.Runtime.EvmStackPopDeclarationFrame
import InitECandidate.Runtime.InterpreterFundingOperandStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The concrete single stack-counter write preserves every live frame's
regular-gas funding words by the existing real record separation. -/
theorem interpreter_funding_after_stack_counter {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (index : BitVec 64)
 (memory : post.memory=(sourceWriteWord s (current.address+16) index).memory)
 (domain : post.memaddrs=s.memaddrs) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 constructor
 · exact layout.upperBound
 · intro record present
   apply (layout.records record present).after_frame domain
   intro offset member
   have separate:=interpreter_funding_stack_headers_distinct s _ upper current record ancestors layout present offset 16 member (by simp)
   change record.address+offset≠current.address+16#64 at separate
   rw [memory]
   change (if record.address+offset=current.address+16#64 then _ else _)=_
   rw [if_neg separate]
 · exact layout.disjoint
 · exact layout.budget
#print axioms interpreter_funding_after_stack_counter
end InitECandidate.Runtime
