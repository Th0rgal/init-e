import InitECandidate.Runtime.SSALoopQuantitativeEntry
import InitECandidate.Runtime.SSALoopRecursiveCost
import InitECandidate.Runtime.SSALoopTimeoutCost
import InitECandidate.Runtime.SSALoopExitCost

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

/-- Complete quantitative simulation of the emitted loop, before its
one-off setup. The only semantic induction premise concerns the smaller
source body. Recursive loop reasoning is discharged by clock induction. -/
theorem ssa_loop_quantitative_context {C F : Type} (ctx : SSALoopCostContext)
    (next : Nat)
    (produced : ssaCcTrans ctx.body (sptInter ctx.refreshed ctx.names) next
      ((ctx.refreshed,ctx.names,ctx.exits)::ctx.tables) = (ctx.output,ctx.mapOut,ctx.nextOut))
    (valid : ssaMapOK next ctx.refreshed) (allocated : isAllocVar next)
    (vars : everyVarHOL (fun key => decide (key < next)) ctx.body = true)
    (entryInjection : ∀ x y, sptDomain ctx.names x → sptDomain ctx.names y →
      optionLookup ctx.refreshed x = optionLookup ctx.refreshed y → x = y)
    (exitInjection : ∀ x y, sptDomain ctx.exits x → sptDomain ctx.exits y →
      optionLookup ctx.refreshed x = optionLookup ctx.refreshed y → x = y)
    (namesMapped : ∀ key, sptDomain ctx.names key → sptDomain ctx.refreshed key)
    (exitsMapped : ∀ key, sptDomain ctx.exits key → sptDomain ctx.refreshed key)
    (namesBound : ∀ key, sptDomain ctx.names key → key < next)
    (exitsBound : ∀ key, sptDomain ctx.exits key → key < next)
    (tableValid : ltOK ctx.tables)
    (seqZero : ∀ a b, ctx.TP (.seq a b) = 0)
    (headCost : ctx.TP ctx.targetLoop + ctx.TP ctx.moves ≤ ctx.SP ctx.sourceLoop)
    (bodyIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat)
      (counter : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel counter map source.locals target.locals ∧ isAllocVar counter ∧
      everyVarHOL (fun key => decide (key < counter)) ctx.body = true ∧
      ssaMapOK counter map ∧ ltOK tables →
      SSAQuantitativeSimulation ctx.SP ctx.TP ctx.body source target map counter tables)
    (source target : WordSemStateFiniteExact 64 C F)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
      (sptDomain ctx.names) source.locals target.locals) :
    ∀ targetResult targetFinal, evaluate ctx.targetLoop target = (targetResult,targetFinal) →
      SSALoopQuantitativePost ctx source target targetFinal targetResult := by
  have headOnly : ctx.TP ctx.targetLoop ≤ ctx.SP ctx.sourceLoop :=
    Nat.le_trans (Nat.le_add_right _ _) headCost
  have solve : ∀ clock, ∀ source target : WordSemStateFiniteExact 64 C F,
      target.clock = clock → Flapjack.WordAlloc.wordStateEqRel source target →
      Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
        (sptDomain ctx.names) source.locals target.locals →
      ∀ targetResult targetFinal, evaluate ctx.targetLoop target = (targetResult,targetFinal) →
        SSALoopQuantitativePost ctx source target targetFinal targetResult := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock ih =>
      intro source target clockEq frame strong targetResult targetFinal loopRun
      have recursiveIH : ∀ nextSource nextTarget : WordSemStateFiniteExact 64 C F,
          nextTarget.clock < target.clock →
          Flapjack.WordAlloc.wordStateEqRel nextSource nextTarget ∧
          Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
            (sptDomain ctx.names) nextSource.locals nextTarget.locals ∧
          (∀ key, sptDomain ctx.names key → sptDomain nextTarget.locals (optionLookup ctx.refreshed key)) →
          ∀ nextResult nextFinal, evaluate ctx.targetLoop nextTarget = (nextResult,nextFinal) →
            SSALoopQuantitativePost ctx nextSource nextTarget nextFinal nextResult := by
        intro nextSource nextTarget strict input nextResult nextFinal nextRun
        exact ih nextTarget.clock (by rwa [← clockEq]) nextSource nextTarget rfl input.1 input.2.1
          nextResult nextFinal nextRun
      cases sourceCut : wordSemCutEnv (ctx.names,.ln) source.locals with
      | none =>
        have stateCut : cutState (ctx.names,.ln) {source with permute := target.permute} = none := by
          unfold cutState
          dsimp only
          rw [sourceCut]
        have failed : evaluate ctx.sourceLoop {source with permute := target.permute} =
            (some .error,{source with permute := target.permute}) := by
          simp only [SSALoopCostContext.sourceLoop,evaluate_def_rebound,stateCut]
        exact post_of_run ctx source _ target targetFinal _ targetResult target.permute failed (Or.inl rfl)
      | some sourceEnv =>
        obtain ⟨targetEnv,targetCut,domain,simulation⟩ := ssa_loop_quantitative_entry ctx.SP ctx.TP
          source target ctx.refreshed next ctx.names ctx.exits ctx.body ctx.tables sourceEnv frame strong
          valid allocated vars entryInjection exitInjection namesMapped namesBound tableValid bodyIH sourceCut
        obtain ⟨permutation,bodyPost⟩ := simulation
        dsimp only at bodyPost
        rw [produced] at bodyPost
        cases sourceBody : evaluate ctx.body {source with locals := sourceEnv,permute := permutation} with
        | mk sourceResult sourceAfter =>
          cases targetBody : evaluate ctx.output {target with locals := targetEnv} with
          | mk targetBodyResult targetAfter =>
            rw [sourceBody,targetBody] at bodyPost
            dsimp only at bodyPost
            have sourceStateCut : cutState (ctx.names,.ln) {source with permute := permutation} =
                some {source with locals := sourceEnv,permute := permutation} := by
              unfold cutState
              dsimp only
              rw [sourceCut]
            have targetStateCut : cutState (ctx.targetNames,.ln) target =
                some {target with locals := targetEnv} := by
              unfold cutState
              rw [targetCut]
            rcases bodyPost with error | ⟨resultEqual,bodyFrame,bodyLocals,bodyCost⟩
            · subst sourceResult
              have actual := WordToWord.evaluate_loop_run ctx.names ctx.exits ctx.body
                {source with permute := permutation} {source with locals := sourceEnv,permute := permutation}
                sourceStateCut (some .error) sourceAfter sourceBody
              have failed : evaluate ctx.sourceLoop {source with permute := permutation} =
                  (some .error,sourceAfter) := by
                simpa [wordSemContLoop,wordSemExitLoop] using actual
              exact post_of_run ctx source _ target targetFinal _ targetResult permutation failed (Or.inl rfl)
            · subst targetBodyResult
              cases sourceResult with
              | none =>
                obtain ⟨reconciled,finalRun,finalFrame,entryLocals,finalCost⟩ :=
                  ssa_body_none_reconcile_exact_cost ctx.TP seqZero sourceAfter
                    {target with locals := targetEnv} targetAfter ctx.output ctx.mapOut ctx.refreshed
                    ctx.nextOut ctx.names targetBody bodyFrame bodyLocals entryInjection
                have finalRun' : evaluate ctx.finalBody {target with locals := targetEnv} = (none,reconciled) := by
                  unfold SSALoopCostContext.finalBody SSALoopCostContext.moves
                  generalize moveEq : ssaReconcile (width := 64) ctx.mapOut ctx.refreshed ctx.names = moves at finalRun ⊢
                  cases moves <;> exact finalRun
                have finalCost' : wordExecutionCost (fun p _ => ctx.TP p) ctx.finalBody
                    {target with locals := targetEnv} ≤
                    wordExecutionCost (fun p _ => ctx.TP p) ctx.output {target with locals := targetEnv} + ctx.TP ctx.moves := by
                  unfold SSALoopCostContext.finalBody SSALoopCostContext.moves
                  generalize moveEq : ssaReconcile (width := 64) ctx.mapOut ctx.refreshed ctx.names = moves at finalCost ⊢
                  cases moves <;> exact finalCost
                have bound := Nat.le_trans finalCost' (Nat.add_le_add_right bodyCost (ctx.TP ctx.moves))
                exact ssa_loop_recursive_outcome ctx source target sourceAfter reconciled targetFinal
                  sourceEnv targetEnv none targetResult permutation sourceCut targetCut sourceBody finalRun'
                  finalFrame entryLocals rfl loopRun bound headCost recursiveIH
              | some value =>
                obtain ⟨finalRun,finalCost⟩ := ssa_body_terminal_reconcile ctx.TP seqZero ctx.output ctx.moves
                  {target with locals := targetEnv} targetAfter value targetBody
                by_cases continueZero : value = .continue 0
                · subst value
                  have entryLocals : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
                      (sptDomain ctx.names) sourceAfter.locals targetAfter.locals := by
                    simpa [SSAResultLocals] using bodyLocals
                  have bound : wordExecutionCost (fun p _ => ctx.TP p) ctx.finalBody
                      {target with locals := targetEnv} ≤
                      wordExecutionCost (fun p _ => ctx.SP p) ctx.body
                        {source with locals := sourceEnv,permute := permutation} + ctx.TP ctx.moves := by
                    exact Nat.le_trans (Nat.le_trans (Nat.le_of_eq finalCost) bodyCost)
                      (Nat.le_add_right _ _)
                  exact ssa_loop_recursive_outcome ctx source target sourceAfter targetAfter targetFinal
                    sourceEnv targetEnv (some (.continue 0)) targetResult permutation sourceCut targetCut
                    sourceBody finalRun bodyFrame entryLocals rfl loopRun bound headCost recursiveIH
                · by_cases breakZero : value = .break 0
                  · subst value
                    cases exitCut : wordSemCutEnv (ctx.exits,.ln) sourceAfter.locals with
                    | none =>
                      have stateExit : cutState (ctx.exits,.ln) sourceAfter = none := by
                        unfold cutState
                        rw [exitCut]
                      have actual := WordToWord.evaluate_loop_run ctx.names ctx.exits ctx.body
                        {source with permute := permutation} {source with locals := sourceEnv,permute := permutation}
                        sourceStateCut (some (.break 0)) sourceAfter sourceBody
                      have failed : evaluate ctx.sourceLoop {source with permute := permutation} =
                          (some .error,sourceAfter) := by
                        simpa only [wordSemContLoop,Bool.false_eq_true,if_false,if_true,stateExit] using actual
                      exact post_of_run ctx source _ target targetFinal _ targetResult permutation failed (Or.inl rfl)
                    | some exitEnv =>
                      have exitStrong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ctx.refreshed)
                          (sptDomain ctx.exits) sourceAfter.locals targetAfter.locals := by
                        simpa [SSAResultLocals] using bodyLocals
                      obtain ⟨targetExitEnv,sourceActual,targetActual,exitFrame,exitLocals,cost⟩ :=
                        ssa_loop_break_zero_cost ctx.SP ctx.TP seqZero ctx.names ctx.exits ctx.refreshed
                          ctx.mapOut next ctx.nextOut ctx.body ctx.output ctx.moves ctx.tables
                          {source with permute := permutation} {source with locals := sourceEnv,permute := permutation}
                          sourceAfter target {target with locals := targetEnv} targetAfter exitEnv produced
                          valid allocated sourceStateCut targetStateCut sourceBody targetBody bodyFrame exitStrong
                          exitInjection exitsMapped exitsBound exitCut bodyCost headOnly
                      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (targetActual.symm.trans loopRun)
                      exact post_of_run ctx source _ target _ _ _ permutation sourceActual
                        (Or.inr ⟨rfl,exitFrame,exitLocals,cost⟩)
                  · have terminal : wordSemContLoop (some value) = false := by
                      cases value <;> try rfl
                      rename_i label
                      have nz : label ≠ 0 := fun equal => continueZero (by rw [equal])
                      simp [wordSemContLoop,nz]
                    have notExit : (some value : Option (WordSemResult 64)) ≠ some (.break 0) :=
                      fun equal => breakZero (Option.some.inj equal)
                    obtain ⟨sourceActual,targetActual,cost⟩ := ssa_loop_terminal_cost ctx.SP ctx.TP seqZero
                      ctx.names ctx.exits ctx.targetNames ctx.targetExits ctx.body ctx.output ctx.moves
                      {source with permute := permutation} {source with locals := sourceEnv,permute := permutation}
                      sourceAfter target {target with locals := targetEnv} targetAfter value sourceStateCut targetStateCut
                      sourceBody targetBody terminal notExit bodyCost headOnly
                    have finalLocals := ssa_loop_terminal_locals ctx.nextOut ctx.nextOut ctx.mapOut
                      (sptInter ctx.refreshed ctx.exits) ctx.refreshed ctx.names ctx.exits ctx.tables
                      sourceAfter.locals targetAfter.locals (some value) bodyLocals terminal notExit
                    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (targetActual.symm.trans loopRun)
                    exact post_of_run ctx source _ target _ _ _ permutation sourceActual
                      (Or.inr ⟨rfl,bodyFrame,finalLocals,cost⟩)
  exact solve target.clock source target rfl frame strong

#print axioms ssa_loop_quantitative_context
#print axioms ssa_loop_recursive_outcome
end InitECandidate.Runtime.FineCost
