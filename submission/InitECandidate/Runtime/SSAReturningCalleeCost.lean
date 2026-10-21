import InitECandidate.Runtime.WordStackValueGlobalCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Actual returning-call callee transport with its executed cost. The source
root permutation and target entry are derived from the original cut ownership
and handler invariants. The body is unchanged by this one-body SSA pass;
whole saved-stack-value transport discharges its cost without a callee IH. -/
theorem returningCalleeTransport_cost  {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (prices : ∀ p, TP p ≤ SP p)
    (source target : WordSemStateFiniteExact 64 C F)
    (sourceFirst sourceSecond targetFirst targetSecond : Spt (WordLocW 64))
    (f : Nat → Nat)
    (handler targetHandler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (args : List (WordLocW 64)) (size : Option Nat) (body : WordLangProgHOL (BitVec 64))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (firstDomain : sptDomain targetFirst =
      (fun key => ∃ name, sptDomain sourceFirst name ∧ f name = key))
    (secondDomain : sptDomain targetSecond =
      (fun key => ∃ name, sptDomain sourceSecond name ∧ f name = key))
    (firstInjective : ∀ a b, sptDomain sourceFirst a → sptDomain sourceFirst b → f a = f b → a = b)
    (secondInjective : ∀ a b, sptDomain sourceSecond a → sptDomain sourceSecond b → f a = f b → a = b)
    (secondRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain sourceSecond)
      sourceSecond targetSecond)
    (handlerAligned : match handler with
      | none => targetHandler = none
      | some (_,_,l1,l2) => match targetHandler with
        | none => False
        | some (_,_,r1,r2) => r1 = l1 ∧ r2 = l2) :
    ∃ perm,
      let sourceEntry := WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (sourceFirst,sourceSecond) handler
          {WordSemStateFiniteExact.decClock source with permute := perm});
      let targetEntry := WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) targetHandler
          (WordSemStateFiniteExact.decClock target));
      (wordSemEnvToList sourceSecond perm).2 = (wordSemEnvToList targetSecond target.permute).2 ∧
      {sourceEntry with stack := targetEntry.stack} = targetEntry ∧
      WordSemStackEq.sValEq sourceEntry.stack targetEntry.stack ∧
      WordSemStackEq.stackSwapPost body sourceEntry ∧
      ((evaluate body sourceEntry).1 ≠ some .error →
        wordExecutionCost (fun p _ => TP p) body targetEntry ≤
          wordExecutionCost (fun p _ => SP p) body sourceEntry) := by
  obtain ⟨perm, roots, entry, values, swapped⟩ := returningCalleeTransport source target
    sourceFirst sourceSecond targetFirst targetSecond f handler targetHandler args size body
    frame firstDomain secondDomain firstInjective secondInjective secondRelated (by
      cases handler with
      | none => exact handlerAligned
      | some payload =>
        rcases payload with ⟨name, program, l1, l2⟩
        cases targetHandler with
        | none => exact handlerAligned
        | some payload =>
          rcases payload with ⟨targetName, targetProgram, r1, r2⟩
          exact handlerAligned)
  refine ⟨perm, roots, entry, values, swapped, ?_⟩
  intro safe
  have cost := word_stack_value_executed_cost SP body
    (callEnv args size (pushEnv (sourceFirst, sourceSecond) handler {decClock source with permute := perm}))
    safe _ values
  have mono := wordExecutionCost_mono (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
    (fun p _ => SP p) (fun p _ => prices p) body
    (callEnv args size (pushEnv (targetFirst, targetSecond) targetHandler (decClock target)))
  rw [entry] at cost
  exact mono.trans (Nat.le_of_eq cost)

#print axioms returningCalleeTransport_cost
end InitECandidate.Runtime.FineCost
