import InitECandidate.Runtime.InterpreterFundingMemoryTransport
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- Concrete funding survives a step that keeps the domain and touches only the
two operand-header words at `address+0` and `address+16`; every funding word
lives at offsets 64..192, so the whole registry is preserved. -/
theorem InterpreterFundingLayout.after_header_frame {F : Type}
 {s post : PanSemStateFiniteExact 64 F}
 {upper : Nat} {current : InterpreterFundingFrame} {ancestors : List InterpreterFundingFrame}
 (valid : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (domain : post.memaddrs=s.memaddrs)
 (memory : ∀watched : BitVec 64,current.address.toNat≤watched.toNat→watched≠current.address+0→watched≠current.address+16→post.memory watched=s.memory watched) :
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
 · exact valid.disjoint
 · exact valid.budget
#print axioms InterpreterFundingLayout.after_header_frame
end InitECandidate.Runtime
