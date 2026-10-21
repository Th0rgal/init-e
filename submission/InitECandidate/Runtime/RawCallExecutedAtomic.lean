import InitECandidate.Runtime.RawCallExecutedReturning
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open InitECandidate.Runtime.StackToLab

/-- Nodes with no recursive execution-counter subterms. -/
def rawCostAtomic : HolProg 64 → Bool
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .call _ _ _ | .rawCall _ | .jumpLower _ _ _ => false
  | _ => true

theorem rawCostAtomic_cost {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (atomic : rawCostAtomic p = true) :
    stackExecutionCost (fun p _ => price p) p source = price p := by
  cases p <;> simp_all [rawCostAtomic, stackExecutionCost]

/-- Atomic cases use the original compiler's semantic witness. Their actual
execution counter is precisely their local price at every witness clock. -/
theorem executed_atomic {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64)) (atomic : rawCostAtomic p = true)
    (hypothesis : StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (compTop info p) info target post result
      (stackExecutionCost (fun p _ => price p) p source) ∧
    ExecutedSimulationResult price (comp info p) info target post result
      (stackExecutionCost (fun p _ => price p) p source) := by
  have identities : compTop info p = p ∧ comp info p = p := by
    cases p <;> simp_all [rawCostAtomic, compTop, comp]
  obtain ⟨top, body⟩ := Flapjack.Compiler.Backend.StackRawCall.FullCompCorrect.compCorrect p source target info result post hypothesis
  constructor
  · obtain ⟨clock, final, space, relation, run, guard⟩ := top
    refine ⟨clock, final, space, relation, run, guard, ?_⟩
    rw [identities.1, rawCostAtomic_cost price p _ atomic, rawCostAtomic_cost price p source atomic]
  · obtain ⟨clock, final, space, relation, run, guard⟩ := body
    refine ⟨clock, final, space, relation, run, guard, ?_⟩
    rw [identities.2, rawCostAtomic_cost price p _ atomic, rawCostAtomic_cost price p source atomic]

#print axioms rawCostAtomic_cost
#print axioms executed_atomic
end InitECandidate.Runtime.StackRawCall
