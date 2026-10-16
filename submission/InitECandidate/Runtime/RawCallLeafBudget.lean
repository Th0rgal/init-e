import InitECandidate.Runtime.RawCallBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.BasicLeaves
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.ControlLeaves
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.StackAccess
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.MemoryFfi

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

/-- The original basic leaf family has zero extra clock, with the full relation. -/
theorem basic_zero {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (leaf : BasicLeaves.BasicLeaf p) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info p) info target post result ∧
    BoundedSimulationResult (comp info p) info target post result := by
  obtain ⟨run, _, relation⟩ := hypothesis
  obtain ⟨final, postRelation, targetRun⟩ :=
    BasicLeaves.evaluate_stateRel p leaf info source target post result run relation
  exact unchanged_pair p info target post final result
    (by cases leaf <;> rfl) (by cases leaf <;> rfl) postRelation targetRun

/-- The original control leaf family has zero extra clock, with the full relation. -/
theorem control_zero {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (leaf : ControlLeaves.ControlLeaf p) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info p) info target post result ∧
    BoundedSimulationResult (comp info p) info target post result := by
  obtain ⟨run, _, relation⟩ := hypothesis
  obtain ⟨final, postRelation, targetRun⟩ :=
    ControlLeaves.evaluate_stateRel p leaf info source target post result run relation
  exact unchanged_pair p info target post final result
    (by cases leaf <;> rfl) (by cases leaf <;> rfl) postRelation targetRun

/-- The original stack leaf family has zero extra clock, with the full relation. -/
theorem stack_zero {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (leaf : StackAccessCase.StackLeaf p) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info p) info target post result ∧
    BoundedSimulationResult (comp info p) info target post result := by
  obtain ⟨run, _, relation⟩ := hypothesis
  obtain ⟨final, postRelation, targetRun⟩ :=
    StackAccessCase.evaluate_stateRel p leaf info source target post result run relation
  exact unchanged_pair p info target post final result
    (by cases leaf <;> rfl) (by cases leaf <;> rfl) postRelation targetRun

/-- The original memory leaf family has zero extra clock, with the full relation. -/
theorem memory_zero {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (leaf : MemoryFfiCase.MemoryLeaf p) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info p) info target post result ∧
    BoundedSimulationResult (comp info p) info target post result := by
  obtain ⟨run, _, relation⟩ := hypothesis
  obtain ⟨final, postRelation, targetRun⟩ :=
    MemoryFfiCase.evaluate_stateRel p leaf info source target post result run relation
  exact unchanged_pair p info target post final result
    (by cases leaf <;> rfl) (by cases leaf <;> rfl) postRelation targetRun

#print axioms memory_zero
#print axioms stack_zero
end InitECandidate.Runtime.StackRawCall
