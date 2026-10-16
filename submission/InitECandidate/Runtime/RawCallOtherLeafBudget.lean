import InitECandidate.Runtime.RawCallLeafBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.AllocationStore
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Install

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackRawCall

/-! Zero-extra-clock versions of the original label, heap and install cases.
They retain all original premises and both original simulation postconditions. -/
open Flapjack.Compiler.Backend.StackRawCall.StackAccessCase in
theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (register first second : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.locValue register first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.locValue register first second)) info target resultState result ∧
    BoundedSimulationResult (comp info (.locValue register first second)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have labels := locCheck_stateRel info source target relation (first, second)
  rw [StackSemEvaluate.evaluate_locValue] at execution
  split at execution
  · rename_i location
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    obtain ⟨code, domain, equality, frames, entries⟩ := relation
    subst target
    have postRelation : stateRel info (setVar register (.loc first second) source)
        { setVar register (.loc first second) source with code := code } := by
      exact ⟨code, domain, rfl, frames, entries⟩
    have targetLocation : StackSem.locCheckExact code (first, second) := labels.mpr location
    constructor <;>
      refine ⟨0, Nat.le_refl 0, { setVar register (.loc first second) source with code := code },
        (setVar register (.loc first second) source).stackSpace, postRelation, ?_, ?_⟩
    all_goals try (intro _; rfl)
    all_goals simp only [compTop, comp, Nat.add_zero, StackSemEvaluate.evaluate_locValue,
      targetLocation, if_true, setVar]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)

open Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase in
theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.alloc register)) info target post result ∧
    BoundedSimulationResult (comp info (.alloc register)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ := postRelationOfTransport (fun state => StackSemEvaluate.evaluate (.alloc register, state))
      source target post info result (evaluateAlloc_codeUpdate register source) execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, Nat.le_refl 0, targetPost, targetPost.stackSpace, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution

open Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase in
theorem compCorrectStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    BoundedSimulationResult (comp info (.storeConsts first second stub)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ := evaluateStoreConsts_stateRel first second stub info source target post result
      execution nonerror relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, Nat.le_refl 0, targetPost, targetPost.stackSpace, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution
open Flapjack.Compiler.Backend.StackRawCall.InstallCase in
theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    BoundedSimulationResult (comp info (.install ptr len dptr dlen ret)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  obtain ⟨targetPost, postRelation, targetExecution⟩ :=
    evaluateInstall_stateRel ptr len dptr dlen ret info source target post result
      execution nonerror relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, Nat.le_refl 0, targetPost, targetPost.stackSpace, postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution

#print axioms compCorrectInstall
#print axioms compCorrectStoreConsts
#print axioms compCorrectLocValue
end InitECandidate.Runtime.StackRawCall
