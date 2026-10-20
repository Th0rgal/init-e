import InitECandidate.Runtime.WitnessTraversalBodyBound
import InitECandidate.Runtime.DecodeStepInputCapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witnessTraversalIterationCost_mono (n m : Nat) (inside : n≤m) :
    witnessTraversalIterationCost n≤witnessTraversalIterationCost m :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right (decodeStepBodyCost_mono n m inside) 1)
    (Nat.add_le_add_right (resolveStepBodyCost_mono n m inside) 1)) (witness_branch_finish_cost_mono inside)

theorem witnessTraversalLoopCost_mono (n m : Nat) (inside : n≤m) :
    witnessTraversalLoopCost n≤witnessTraversalLoopCost m :=
  Nat.mul_le_mul_left witnessTraversalRankCeiling (Nat.add_le_add_right (witnessTraversalIterationCost_mono n m inside) 1)

/-- A fixed finite source-step ceiling for the original witness decoder body. -/
def witnessTraversalBodySourceCeiling : Nat := witnessTraversalLoopCost 134217712

theorem witnessTraversalBodySourceCeiling_value : witnessTraversalBodySourceCeiling = 1253859727249173895072488284279033423356432986191251770300 := by decide

/-- Every actual decoder-body outcome fits the same numerical ceiling at the
challenge input cap, under the concrete initialized arena/database geometry. -/
theorem runBounded_witness_traversal_body_uniform {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (budget : witnessTraversalBodySourceCeiling≤s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_witness_node_body) witnessTraversalBodySourceCeiling := by
  have costBound := witnessTraversalLoopCost_mono layout.inputLimit 134217712 valid.inputLimitBound
  exact (runBounded_witness_traversal_body layout s scratch heap pointer length valid atPointer atLength
    (costBound.trans budget)).weaken costBound
#print axioms witnessTraversalIterationCost_mono
#print axioms witnessTraversalLoopCost_mono
#print axioms witnessTraversalBodySourceCeiling_value
#print axioms runBounded_witness_traversal_body_uniform
end InitECandidate.Runtime
