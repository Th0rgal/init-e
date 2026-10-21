import InitECandidate.Runtime.WordExecutionCostProps
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Only a valid normal return or a matching exception reaches a continuation. -/
noncomputable def wordReturningContinuationCost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (values : List Nat) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (result : Option (WordSemResult 64)) (post : WordSemStateFiniteExact 64 C F) : Nat :=
  match result with
  | some (.result location returned) =>
      if location ≠ .loc l1 l2 ∨ returned.length ≠ values.length then 0 else
        match popEnv post with
        | none => 0
        | some popped => if sptDomainEqUnion popped.locals envs.1 envs.2 then
            wordExecutionCost price retCode (setVars values returned popped) else 0
  | some (.exception location value) =>
      match handler with
      | none => 0
      | some (reg,code,h1,h2) => if location ≠ .loc h1 h2 then 0 else
          if sptDomainEqUnion post.locals envs.1 envs.2 then
            wordExecutionCost price code (setVar reg value post) else 0
  | _ => 0

/-- Exact executed call decomposition: local work, reached callee, and only
its selected continuation. Guard facts come from the actual source run. -/
theorem wordExecutionCost_returning {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 (Nat × C) F → Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × C) F)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : Flapjack.WordToStackProofs.CompCorrect.CallReturning.SourceGuards
      values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (bodyResult : Option (WordSemResult 64)) (bodyPost : WordSemStateFiniteExact 64 (Nat × C) F)
    (bodyRun : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock source))) =
      (bodyResult,bodyPost)) :
    wordExecutionCost price (.call (some (values,names,retCode,l1,l2)) dest args handler) source =
      price (.call (some (values,names,retCode,l1,l2)) dest args handler) source +
      wordExecutionCost price prog (callEnv args1 ss (pushEnv envs handler (decClock source))) +
      wordReturningContinuationCost price values retCode l1 l2 handler envs bodyResult bodyPost := by
  rcases guards with ⟨get,bad,find,valid,cut⟩
  rw [wordExecutionCost]
  simp only [get,bad,Bool.false_eq_true,↓reduceIte,find,valid,cut,nonzero,dite_false,
    ]
  rw [WordSemStateFiniteExact.fix_clock_evaluate,bodyRun]
  cases bodyResult with
  | none => rfl
  | some result =>
      cases result <;> simp only [wordReturningContinuationCost]
      all_goals repeat' first | (solve | simp_all [wordReturningContinuationCost]) | split

#print axioms wordExecutionCost_returning
end InitECandidate.Runtime.FineCost
