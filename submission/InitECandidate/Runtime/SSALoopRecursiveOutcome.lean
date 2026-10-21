import InitECandidate.Runtime.SSALoopQuantitativeEntry
import InitECandidate.Runtime.SSALoopRecursiveCost
import InitECandidate.Runtime.SSALoopTimeoutCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Fixed syntax and output relation for one actual SSA loop. The enclosing
compiler theorem supplies its compilation equation and body induction proof. -/
structure SSALoopCostContext where
  SP : WordLangProgHOL (BitVec 64) → Nat
  TP : WordLangProgHOL (BitVec 64) → Nat
  names : Spt Unit
  exits : Spt Unit
  refreshed : Spt Nat
  mapOut : Spt Nat
  nextOut : Nat
  body : WordLangProgHOL (BitVec 64)
  output : WordLangProgHOL (BitVec 64)
  tables : List (Spt Nat × Spt Unit × Spt Unit)

namespace SSALoopCostContext
abbrev moves (ctx : SSALoopCostContext) :=
  ssaReconcile (width := 64) ctx.mapOut ctx.refreshed ctx.names
abbrev finalBody (ctx : SSALoopCostContext) :=
  match (generalizing := false) ctx.moves with | .skip => ctx.output | _ => .seq ctx.output ctx.moves
abbrev sourceLoop (ctx : SSALoopCostContext) : WordLangProgHOL (BitVec 64) := .loop ctx.names ctx.body ctx.exits
abbrev targetNames (ctx : SSALoopCostContext) :=
  Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.names
abbrev targetExits (ctx : SSALoopCostContext) :=
  Flapjack.WordAlloc.applyNummapKey (optionLookup ctx.refreshed) ctx.exits
abbrev targetLoop (ctx : SSALoopCostContext) : WordLangProgHOL (BitVec 64) := .loop ctx.targetNames ctx.finalBody ctx.targetExits
end SSALoopCostContext

/-- Same-witness quantitative loop conclusion, before the one-off setup. -/
def SSALoopQuantitativePost {C F : Type} (ctx : SSALoopCostContext)
    (source target targetFinal : WordSemStateFiniteExact 64 C F)
    (targetResult : Option (WordSemResult 64)) : Prop :=
  ∃ permutation,
    let run := evaluate ctx.sourceLoop {source with permute := permutation}
    run.1 = some .error ∨ run.1 = targetResult ∧
      Flapjack.WordAlloc.wordStateEqRel run.2 targetFinal ∧
      SSAResultLocals ctx.nextOut (sptInter ctx.refreshed ctx.exits) ctx.tables
        run.2.locals targetFinal.locals run.1 ∧
      wordExecutionCost (fun p _ => ctx.TP p) ctx.targetLoop target ≤
        wordExecutionCost (fun p _ => ctx.SP p) ctx.sourceLoop {source with permute := permutation}

private theorem post_of_run {C F : Type} (ctx : SSALoopCostContext)
    (source after target targetFinal : WordSemStateFiniteExact 64 C F)
    (result targetResult : Option (WordSemResult 64)) (permutation : Nat → Nat → Nat)
    (run : evaluate ctx.sourceLoop {source with permute := permutation} = (result,after))
    (related : result = some .error ∨ result = targetResult ∧
      Flapjack.WordAlloc.wordStateEqRel after targetFinal ∧
      SSAResultLocals ctx.nextOut (sptInter ctx.refreshed ctx.exits) ctx.tables
        after.locals targetFinal.locals result ∧
      wordExecutionCost (fun p _ => ctx.TP p) ctx.targetLoop target ≤
        wordExecutionCost (fun p _ => ctx.SP p) ctx.sourceLoop {source with permute := permutation}) :
    SSALoopQuantitativePost ctx source target targetFinal targetResult := by
  refine ⟨permutation,?_⟩
  dsimp only
  rw [run]
  exact related

/-- Complete continuing branch of the actual SSA loop clock induction.
It handles timeout, failed source re-entry, and a successful recursive IH,
while preserving one permutation for semantics and executed work. -/
theorem ssa_loop_recursive_outcome {C F : Type} (ctx : SSALoopCostContext)
    (source target sourceAfter targetAfter targetFinal : WordSemStateFiniteExact 64 C F)
    (sourceEnv targetEnv : Spt (WordLocW 64))
    (bodyResult targetResult : Option (WordSemResult 64)) (permutation : Nat → Nat → Nat)
    (sourceCut : wordSemCutEnv (ctx.names,.ln) source.locals = some sourceEnv)
    (targetCut : wordSemCutEnv (ctx.targetNames,.ln) target.locals = some targetEnv)
    (sourceRun : evaluate ctx.body {source with locals := sourceEnv,permute := permutation} =
      (bodyResult,sourceAfter))
    (targetRun : evaluate ctx.finalBody {target with locals := targetEnv} = (bodyResult,targetAfter))
    (frame : Flapjack.WordAlloc.wordStateEqRel sourceAfter targetAfter)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
      (sptDomain ctx.names) sourceAfter.locals targetAfter.locals)
    (continuing : wordSemContLoop bodyResult = true)
    (loopRun : evaluate ctx.targetLoop target = (targetResult,targetFinal))
    (bodyCost : wordExecutionCost (fun p _ => ctx.TP p) ctx.finalBody {target with locals := targetEnv} ≤
      wordExecutionCost (fun p _ => ctx.SP p) ctx.body
        {source with locals := sourceEnv,permute := permutation} + ctx.TP ctx.moves)
    (headCost : ctx.TP ctx.targetLoop + ctx.TP ctx.moves ≤ ctx.SP ctx.sourceLoop)
    (ih : ∀ nextSource nextTarget : WordSemStateFiniteExact 64 C F,
      nextTarget.clock < target.clock →
      Flapjack.WordAlloc.wordStateEqRel nextSource nextTarget ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
        (sptDomain ctx.names) nextSource.locals nextTarget.locals ∧
      (∀ key, sptDomain ctx.names key → sptDomain nextTarget.locals (optionLookup ctx.refreshed key)) →
      ∀ nextResult nextFinal, evaluate ctx.targetLoop nextTarget = (nextResult,nextFinal) →
        SSALoopQuantitativePost ctx nextSource nextTarget nextFinal nextResult) :
    SSALoopQuantitativePost ctx source target targetFinal targetResult := by
  have sourceStateCut : cutState (ctx.names,.ln) {source with permute := permutation} =
      some {source with locals := sourceEnv,permute := permutation} := by
    unfold cutState
    dsimp only
    rw [sourceCut]
  have targetStateCut : cutState (ctx.targetNames,.ln) target =
      some {target with locals := targetEnv} := by
    unfold cutState
    rw [targetCut]
  have targetLoop := WordToWord.evaluate_loop_run ctx.targetNames ctx.targetExits ctx.finalBody
    target {target with locals := targetEnv} targetStateCut bodyResult targetAfter targetRun
  have clocks : targetAfter.clock = sourceAfter.clock := frame.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases zero : targetAfter.clock = 0
  · have sourceZero := clocks.symm.trans zero
    obtain ⟨sourceActual,targetActual,flushed,locals,cost⟩ := ssa_loop_timeout_cost ctx.SP ctx.TP
      ctx.names ctx.exits ctx.targetNames ctx.targetExits ctx.body ctx.finalBody
      {source with permute := permutation} {source with locals := sourceEnv,permute := permutation}
      sourceAfter target {target with locals := targetEnv} targetAfter bodyResult (ctx.TP ctx.moves)
      sourceStateCut targetStateCut sourceRun targetRun continuing sourceZero frame bodyCost headCost
    have same := Prod.mk.inj (targetActual.symm.trans loopRun)
    obtain ⟨rfl,rfl⟩ := same
    exact post_of_run ctx source _ target _ _ _ permutation sourceActual
      (Or.inr ⟨rfl,flushed,locals,cost⟩)
  · have sourceNonzero : sourceAfter.clock ≠ 0 := fun equal => zero (clocks.trans equal)
    cases recursiveCut : wordSemCutEnv (ctx.names,.ln) sourceAfter.locals with
    | none =>
      have sourceLoop := WordToWord.evaluate_loop_run ctx.names ctx.exits ctx.body
        {source with permute := permutation} {source with locals := sourceEnv,permute := permutation}
        sourceStateCut bodyResult sourceAfter sourceRun
      have failedCut : cutState (ctx.names,.ln) (decClock sourceAfter) = none := by
        unfold cutState
        dsimp only [decClock]
        rw [recursiveCut]
      have failed : evaluate ctx.sourceLoop {source with permute := permutation} =
          (some .error,decClock sourceAfter) := by
        rw [sourceLoop]
        simp only [continuing,if_true,sourceNonzero,if_false,wordSemSTOP]
        simp only [SSALoopCostContext.sourceLoop,evaluate_def_rebound,failedCut]
      exact post_of_run ctx source _ target _ _ _ permutation failed (Or.inl rfl)
    | some recursiveEnv =>
      obtain ⟨strict,nextFrame,nextStrong,images⟩ := ssa_loop_recursive_entry ctx.refreshed ctx.names
        ctx.finalBody target sourceAfter targetAfter targetEnv recursiveEnv bodyResult targetRun frame strong recursiveCut zero
      have recursiveTargetRun : evaluate ctx.targetLoop (decClock targetAfter) = (targetResult,targetFinal) := by
        have actual : evaluate ctx.targetLoop target = evaluate ctx.targetLoop (decClock targetAfter) := by
          simpa only [continuing,if_true,zero,if_false,wordSemSTOP] using targetLoop
        exact actual.symm.trans loopRun
      obtain ⟨recursivePermutation,post⟩ := ih (decClock sourceAfter) (decClock targetAfter) strict
        ⟨nextFrame,nextStrong,images⟩ targetResult targetFinal recursiveTargetRun
      dsimp only at post
      cases recursiveSourceRun : evaluate ctx.sourceLoop
          {(decClock sourceAfter) with permute := recursivePermutation} with
      | mk recursiveResult recursiveAfter =>
        rw [recursiveSourceRun] at post
        have notError : bodyResult ≠ some .error := by
          intro error
          rw [error] at continuing
          simp [wordSemContLoop] at continuing
        obtain ⟨outerPermutation,outerRun,outerCost⟩ := stitch_recursive_loop_cost ctx.SP
          {source with permute := permutation} sourceAfter recursiveAfter ctx.names ctx.exits ctx.body
          sourceEnv bodyResult recursiveResult recursivePermutation sourceCut sourceRun notError continuing
          sourceNonzero recursiveSourceRun
        apply post_of_run ctx source recursiveAfter target targetFinal recursiveResult targetResult outerPermutation outerRun
        rcases post with error | ⟨resultEqual,finalFrame,finalLocals,recursiveCost⟩
        · exact Or.inl error
        · refine Or.inr ⟨resultEqual,finalFrame,finalLocals,?_⟩
          have targetCost := pure_loop_cost_run ctx.TP ctx.targetNames ctx.targetExits ctx.finalBody
            target {target with locals := targetEnv} targetAfter bodyResult targetStateCut targetRun
          rw [targetCost,outerCost]
          simp only [continuing,if_true,zero,if_false]
          dsimp only [SSALoopCostContext.targetLoop,SSALoopCostContext.sourceLoop] at *
          omega

#print axioms ssa_loop_recursive_outcome
end InitECandidate.Runtime.FineCost
