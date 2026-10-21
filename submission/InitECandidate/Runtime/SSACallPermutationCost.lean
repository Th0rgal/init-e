import InitECandidate.Runtime.WordPermuteGlobalCost
import InitECandidate.Runtime.WordCallExecutionCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Call
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Cost-aware version of the allocator's final-oracle predicate stitching.
It chooses an initial oracle meeting the selected continuation predicate and
preserves the SAME actual callee's executed cost. Error-exempt calls retain
their original scheduler; no arbitrary permutation-cost invariance is used. -/
theorem ssa_permute_predicate_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (P : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F → Prop)
    (errorP : ∀ post, evaluate program source = (some .error, post) → P (some .error, post))
    (outcome : ∃ permutation, P ((evaluate program source).1,
      {(evaluate program source).2 with permute := permutation})) :
    ∃ permutation, P (evaluate program {source with permute := permutation}) ∧
      wordExecutionCost (fun p _ => price p) program {source with permute := permutation} =
        wordExecutionCost (fun p _ => price p) program source := by
  rcases actual : evaluate program source with ⟨result, post⟩
  by_cases error : result = some .error
  · subst result
    exact ⟨source.permute, by simpa only [actual] using errorP post actual, rfl⟩
  · obtain ⟨finalPermutation, predicate⟩ := outcome
    obtain ⟨initialPermutation, run, work⟩ := word_permute_executed_cost price program source
      finalPermutation (by simpa only [actual] using error)
    refine ⟨initialPermutation, ?_, work⟩
    rw [run]
    exact predicate

/-- Actual returning-call cost under the allocator's root/suffix oracle
composition. The caller prefix chooses the root permutation and the callee
receives exactly the suffix. Its returned continuation work is the ordinary
executed counter, including selected handlers. This is an equation, with no
assumed target budget or transformed-callee induction premise. -/
theorem ssa_call_suffix_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (returns : List Nat) (names : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 C F) (roots suffix : Nat → Nat → Nat)
    (values calleeArgs : List (WordLocW 64)) (callee : WordLangProgHOL (BitVec 64))
    (size : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (read : getVars arguments source = some values)
    (good : wordSemBadDestArgs dest arguments = false)
    (found : wordSemFindCode dest (.loc l1 l2 :: values) source.code source.stackSize = some (calleeArgs, callee, size))
    (validCut : ¬ (sptDomainEmpty names.1 ∨ ¬ returns.Nodup))
    (cut : wordSemCutEnvs names source.locals = some envs) (clock : source.clock ≠ 0) :
    let sourceEntry := callEnv calleeArgs size (pushEnv envs handler {decClock source with permute := roots})
    let calleeState := {sourceEntry with permute := suffix}
    let calleeRun := evaluate callee calleeState
    wordExecutionCost (fun p _ => price p)
      (.call (some (returns, names, continuation, l1, l2)) dest arguments handler)
      {source with permute := Flapjack.WordAlloc.ppPerm roots suffix} =
      price (.call (some (returns, names, continuation, l1, l2)) dest arguments handler) +
        wordExecutionCost (fun p _ => price p) callee calleeState +
        retCont (fun p _ => price p) returns continuation l1 l2 handler envs calleeRun.1 calleeRun.2 := by
  let caller := {source with permute := Flapjack.WordAlloc.ppPerm roots suffix}
  let entry := callEnv calleeArgs size (pushEnv envs handler {decClock source with permute := roots})
  have shape : callEnv calleeArgs size (pushEnv envs handler (decClock caller)) =
      {entry with permute := suffix} := by
    change callEnv calleeArgs size (pushEnv envs handler
      {decClock source with permute := Flapjack.WordAlloc.ppPerm roots suffix}) = _
    rw [Flapjack.WordAlloc.pushEnv_ppPerm]
    rfl
  have actual := ret_call_cost (fun p (_ : WordSemStateFiniteExact 64 C F) => price p)
    returns names continuation l1 l2 dest arguments handler caller values
    (by rw [getVars_withPermute]; exact read) good calleeArgs callee size found validCut envs cut clock
    (evaluate callee (callEnv calleeArgs size (pushEnv envs handler (decClock caller)))).1
    (evaluate callee (callEnv calleeArgs size (pushEnv envs handler (decClock caller)))).2 rfl
  rw [shape] at actual
  exact actual

#print axioms ssa_permute_predicate_cost
#print axioms ssa_call_suffix_cost
end InitECandidate.Runtime.FineCost
