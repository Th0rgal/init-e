import InitECandidate.Runtime.InterpreterFundingLayout
import InitECandidate.Runtime.MemzeroNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
/-- A real normally completed byte store below the live-record lower frontier
preserves every actual funding word; access failure is not assumed away. -/
theorem interpreter_funding_store_byte_normal {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (lower upper : Nat)
 (frames : List InterpreterFundingFrame)
 (valid : InterpreterFundingLayout s lower upper frames)
 (destination expression : ExpHOL 64) (address value : BitVec 64)
 (below : address.toNat<lower)
 (addressEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) destination=some (.val (.word address)))
 (valueEval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word value)))
 (run : evaluateHOLFiniteState s (.storeByte destination expression)=(none,post)) :
 InterpreterFundingLayout post lower upper frames ∧post.locals=s.locals ∧post.globals=s.globals ∧post.clock=s.clock ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 obtain ⟨cell,rfl⟩:=storeByte_normal s post destination expression address value addressEval valueEval run
 have aligned : (panByteAlignHOL address).toNat≤address.toNat := by
  rw [byteAlign_toNat]
  exact Nat.div_mul_le_self _ _
 refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
 constructor
 · exact valid.upperBound
 · intro frame member
   have record:=valid.records frame member
   apply InterpreterFundingFrameAt.after_frame (post:=sourceWriteByte s address value cell) record rfl
   intro offset included
   have small : offset.toNat<280 := by
    simp only [interpreterFundingOffsets,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with rfl|rfl|rfl|rfl <;>decide
   have natural:=interpreter_funding_offset_natural frame upper record.extent valid.upperBound offset small
   apply sourceWriteByte_memory_other
   intro equal
   have same:=congrArg BitVec.toNat equal
   rw [natural] at same
   have low:=record.lowerBound
   omega
 · exact valid.disjoint
 · exact valid.budget
#print axioms interpreter_funding_store_byte_normal
end InitECandidate.Runtime
