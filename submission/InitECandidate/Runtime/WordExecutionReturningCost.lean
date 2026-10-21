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

/-- Valid normal return selects precisely its restored continuation state. -/
theorem wordReturningContinuationCost_normal {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (values : List Nat) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (post popped : WordSemStateFiniteExact 64 C F)
    (valid : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (pop : popEnv post = some popped)
    (domain : sptDomainEqUnion popped.locals envs.1 envs.2) :
    wordReturningContinuationCost price values retCode l1 l2 handler envs
      (some (.result location returned)) post =
      wordExecutionCost price retCode (setVars values returned popped) := by
  simp only [wordReturningContinuationCost,valid,if_false,pop,domain,if_true]

/-- A matching exception selects precisely the handler at its actual state. -/
theorem wordReturningContinuationCost_exception {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (values : List Nat) (retCode handlerCode : WordLangProgHOL (BitVec 64))
    (l1 l2 reg h1 h2 : Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location value : WordLocW 64) (post : WordSemStateFiniteExact 64 C F)
    (valid : ¬ location ≠ .loc h1 h2)
    (domain : sptDomainEqUnion post.locals envs.1 envs.2) :
    wordReturningContinuationCost price values retCode l1 l2 (some (reg,handlerCode,h1,h2)) envs
      (some (.exception location value)) post =
      wordExecutionCost price handlerCode (setVar reg value post) := by
  simp only [wordReturningContinuationCost,valid,if_false,domain,if_true]

/-- Guarded call decomposition is unique; competing IH instances cannot
select a different callee or caller environment. -/
theorem returningSourceGuards_unique {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × C) F)
    (xs args1 xs' args1' : List (WordLocW 64)) (prog prog' : WordLangProgHOL (BitVec 64))
    (ss ss' : Option Nat) (envs envs' : Spt (WordLocW 64) × Spt (WordLocW 64))
    (first : Flapjack.WordToStackProofs.CompCorrect.CallReturning.SourceGuards
      values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (second : Flapjack.WordToStackProofs.CompCorrect.CallReturning.SourceGuards
      values names retCode l1 l2 dest args source xs' args1' prog' ss' envs') :
    xs' = xs ∧ args1' = args1 ∧ prog' = prog ∧ ss' = ss ∧ envs' = envs := by
  have sameArgs := Option.some.inj (second.1.symm.trans first.1)
  subst xs'
  have sameCode := Option.some.inj (second.2.2.1.symm.trans first.2.2.1)
  have sameEnvs := Option.some.inj (second.2.2.2.2.symm.trans first.2.2.2.2)
  exact ⟨rfl,(Prod.mk.inj sameCode).1,(Prod.mk.inj (Prod.mk.inj sameCode).2).1,
    (Prod.mk.inj (Prod.mk.inj sameCode).2).2,sameEnvs⟩

#print axioms wordExecutionCost_returning
#print axioms wordReturningContinuationCost_normal
#print axioms wordReturningContinuationCost_exception
#print axioms returningSourceGuards_unique
end InitECandidate.Runtime.FineCost
