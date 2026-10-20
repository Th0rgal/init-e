import InitECandidate.Runtime.InterpreterFundingOffsetFrame
import InitECandidate.Runtime.DivisionHelperWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Concrete funding survives a step whose only memory writes land inside a
window region that is disjoint from every funding word of the frame chain.
This is the transport needed by helpers such as `u256_div`, whose real bodies
write only inside the 640-byte `u256_ws` workspace. -/
theorem InterpreterFundingLayout.after_window_frame {F : Type}
 {s post : PanSemStateFiniteExact 64 F}
 {upper : Nat} {current : InterpreterFundingFrame} {ancestors : List InterpreterFundingFrame}
 (valid : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (domain : post.memaddrs=s.memaddrs)
 (window : BitVec 64)
 (outside : ∀ record, record∈(current::ancestors) → ∀ offset, offset∈interpreterFundingOffsets →
   ¬ WS window (record.address+offset))
 (memory : ∀watched : BitVec 64,¬ WS window watched → post.memory watched=s.memory watched) :
 InterpreterFundingLayout post current.address.toNat upper (current::ancestors) := by
 constructor
 · exact valid.upperBound
 · intro record member
   have old:=valid.records record member
   apply InterpreterFundingFrameAt.after_frame (post:=post) old domain
   intro offset included
   exact memory (record.address+offset) (outside record member offset included)
 · exact valid.disjoint
 · exact valid.budget
#print axioms InterpreterFundingLayout.after_window_frame
end InitECandidate.Runtime
