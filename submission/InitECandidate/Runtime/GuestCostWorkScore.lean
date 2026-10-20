import InitECandidate.Runtime.PanCostTotal
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

/-- Scalar score of one typed work event. These are the only numerals a local
site ever introduces: each is one coefficient times the actual recorded size. -/
theorem score_statement (coeff : Work) :
    coeff.score (WorkEvent.statement).units = coeff.statements := by
  simp [Work.score, WorkEvent.units]

theorem score_expression (coeff : Work) :
    coeff.score (WorkEvent.expression).units = coeff.expressions := by
  simp [Work.score, WorkEvent.units]

theorem score_scalar (coeff : Work) (count : Nat) :
    coeff.score (WorkEvent.scalar count).units = coeff.scalarOps * count := by
  simp [Work.score, WorkEvent.units]

theorem score_memory (coeff : Work) (count : Nat) :
    coeff.score (WorkEvent.memory count).units = coeff.memoryAccesses * count := by
  simp [Work.score, WorkEvent.units]

theorem score_copy (coeff : Work) (count : Nat) :
    coeff.score (WorkEvent.copy count).units = coeff.movedWords * count := by
  simp [Work.score, WorkEvent.units]

theorem score_frame (coeff : Work) (count : Nat) :
    coeff.score (WorkEvent.frame count).units = coeff.frameSlots * count := by
  simp [Work.score, WorkEvent.units]

theorem score_transfer (coeff : Work) (count : Nat) :
    coeff.score (WorkEvent.transfer count).units = coeff.transferBytes * count := by
  simp [Work.score, WorkEvent.units]

theorem score_primitive (coeff : Work) (count : Nat) :
    coeff.score (WorkEvent.primitive count).units = coeff.primitiveBlocks * count := by
  simp [Work.score, WorkEvent.units]

theorem score_nativeEvent (coeff : Work) :
    coeff.score (WorkEvent.nativeEvent).units = coeff.nativeEvents := by
  simp [Work.score, WorkEvent.units]

/-- Score of a single-event trace. -/
theorem score_singleton (coeff : Work) (event : WorkEvent) :
    coeff.score (executionWork [event]) = coeff.score event.units := by
  simp [executionWork, Work.plus, Work.score]

/-- Score of a two-event trace. -/
theorem score_pair (coeff : Work) (first second : WorkEvent) :
    coeff.score (executionWork [first, second]) =
      coeff.score first.units + coeff.score second.units := by
  rw [executionWork_score_cons coeff first [second], score_singleton]

/-- A recorded size bound is exactly a score bound for one sized event. -/
theorem score_sized_le (coeff : Work) (upper actual : Nat) (h : actual ≤ upper) :
    coeff.score (WorkEvent.copy actual).units ≤ coeff.movedWords * upper := by
  rw [score_copy]
  exact Nat.mul_le_mul_left _ h

end InitECandidate.Runtime.FineCost

#print axioms InitECandidate.Runtime.FineCost.score_copy
#print axioms InitECandidate.Runtime.FineCost.score_pair
#print axioms InitECandidate.Runtime.FineCost.score_singleton
#print axioms InitECandidate.Runtime.FineCost.score_sized_le
