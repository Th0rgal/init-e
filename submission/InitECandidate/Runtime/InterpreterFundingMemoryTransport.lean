import InitECandidate.Runtime.InterpreterFundingLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- Concrete funding depends only on actual memory words and their domains,
so clock/local scope changes do not alter the physical registry. -/
theorem InterpreterFundingLayout.after_memory {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {lower upper : Nat} {frames : List InterpreterFundingFrame}
 (valid : InterpreterFundingLayout s lower upper frames)
 (memory : post.memory=s.memory) (domain : post.memaddrs=s.memaddrs) :
 InterpreterFundingLayout post lower upper frames := by
 constructor
 · exact valid.upperBound
 · intro record present
   apply (valid.records record present).after_frame domain
   intro offset member
   rw [memory]
 · exact valid.disjoint
 · exact valid.budget
#print axioms InterpreterFundingLayout.after_memory
end InitECandidate.Runtime
