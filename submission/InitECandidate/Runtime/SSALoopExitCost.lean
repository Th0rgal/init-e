import InitECandidate.Runtime.SSALoopBodyEntry
import InitECandidate.Runtime.SSALoopTerminalCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Derive the actual loop exit cut from the emitted body compiler metadata
and the body induction relation, including the output allocation counter. -/
theorem ssa_loop_exit_cut {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (refreshed mapOut : Spt Nat) (next nextOut : Nat) (names exits : Spt Unit)
    (body output : WordLangProgHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (sourceEnv : Spt (WordLocW width))
    (produced : ssaCcTrans body (sptInter refreshed names) next
      ((refreshed,names,exits)::tables) = (output,mapOut,nextOut))
    (valid : ssaMapOK next refreshed) (allocated : isAllocVar next)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
      (sptDomain exits) source.locals target.locals)
    (injective : ∀ x y, sptDomain exits x → sptDomain exits y →
      optionLookup refreshed x = optionLookup refreshed y → x = y)
    (mapped : ∀ key, sptDomain exits key → sptDomain refreshed key)
    (bounded : ∀ key, sptDomain exits key → key < next)
    (cut : wordSemCutEnv (exits,.ln) source.locals = some sourceEnv) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits,.ln)
        target.locals = some targetEnv ∧
      Flapjack.WordAlloc.wordStateEqRel {source with locals := sourceEnv}
        {target with locals := targetEnv} ∧
      ssaLocalsRel nextOut (sptInter refreshed exits) sourceEnv targetEnv := by
  have counter := (ssaCcTransProps body (sptInter refreshed names) next _ output mapOut nextOut
    produced ⟨ssaMapOKInter next refreshed names valid,allocated⟩).1
  obtain ⟨targetEnv,targetCut,_,related⟩ := ssa_loop_entry_cut refreshed exits nextOut
    source.locals target.locals sourceEnv cut strong injective mapped
    (fun key inside => Nat.lt_of_lt_of_le (bounded key inside) counter)
  exact ⟨targetEnv,targetCut,by simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame,related⟩


/-- Successful Break-zero branch of the quantitative loop proof. The actual
compiler metadata derives the target exit cut; only the reached body work is
charged, and the output relation uses the refreshed exit map. -/
theorem ssa_loop_break_zero_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (names exits : Spt Unit) (refreshed mapOut : Spt Nat) (next nextOut : Nat)
    (body output moves : WordLangProgHOL (BitVec 64))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source sourceEntry sourcePost target targetEntry targetPost : WordSemStateFiniteExact 64 C F)
    (exitEnv : Spt (WordLocW 64))
    (produced : ssaCcTrans body (sptInter refreshed names) next
      ((refreshed,names,exits)::tables) = (output,mapOut,nextOut))
    (valid : ssaMapOK next refreshed) (allocated : isAllocVar next)
    (sourceCut : cutState (names,.ln) source = some sourceEntry)
    (targetCut : cutState (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names,.ln)
      target = some targetEntry)
    (sourceRun : evaluate body sourceEntry = (some (.break 0),sourcePost))
    (targetRun : evaluate output targetEntry = (some (.break 0),targetPost))
    (frame : Flapjack.WordAlloc.wordStateEqRel sourcePost targetPost)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
      (sptDomain exits) sourcePost.locals targetPost.locals)
    (injective : ∀ x y, sptDomain exits x → sptDomain exits y →
      optionLookup refreshed x = optionLookup refreshed y → x = y)
    (mapped : ∀ key, sptDomain exits key → sptDomain refreshed key)
    (bounded : ∀ key, sptDomain exits key → key < next)
    (exitCut : wordSemCutEnv (exits,.ln) sourcePost.locals = some exitEnv)
    (bodyCost : wordExecutionCost (fun p _ => TP p) output targetEntry ≤
      wordExecutionCost (fun p _ => SP p) body sourceEntry)
    (headCost : TP (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names)
      (match (generalizing := false) moves with | .skip => output | _ => .seq output moves)
      (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits)) ≤
      SP (.loop names body exits)) :
    let finalBody := match (generalizing := false) moves with | .skip => output | _ => .seq output moves
    ∃ targetExitEnv,
      evaluate (.loop names body exits) source = (none,{sourcePost with locals := exitEnv}) ∧
      evaluate (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names)
        finalBody (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits)) target =
        (none,{targetPost with locals := targetExitEnv}) ∧
      Flapjack.WordAlloc.wordStateEqRel {sourcePost with locals := exitEnv}
        {targetPost with locals := targetExitEnv} ∧
      ssaLocalsRel nextOut (sptInter refreshed exits) exitEnv targetExitEnv ∧
      wordExecutionCost (fun p _ => TP p)
        (.loop (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names)
          finalBody (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits)) target ≤
        wordExecutionCost (fun p _ => SP p) (.loop names body exits) source := by
  dsimp only
  obtain ⟨targetExitEnv,targetExit,exitFrame,exitLocals⟩ :=
    ssa_loop_exit_cut sourcePost targetPost refreshed mapOut next nextOut names exits body output
      tables exitEnv produced valid allocated frame strong injective mapped bounded exitCut
  obtain ⟨finalRun,finalCost⟩ := ssa_body_terminal_reconcile TP seqZero output moves
    targetEntry targetPost (.break 0) targetRun
  have sourceExitState : cutState (exits,.ln) sourcePost = some {sourcePost with locals := exitEnv} := by
    unfold cutState
    rw [exitCut]
  have targetExitState : cutState
      (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits,.ln) targetPost =
      some {targetPost with locals := targetExitEnv} := by
    unfold cutState
    rw [targetExit]
  have sourceLoop := WordToWord.evaluate_loop_run names exits body source sourceEntry sourceCut
    (some (.break 0)) sourcePost sourceRun
  have targetLoop := WordToWord.evaluate_loop_run
    (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names)
    (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits)
    (match (generalizing := false) moves with | .skip => output | _ => .seq output moves)
    target targetEntry targetCut (some (.break 0)) targetPost finalRun
  refine ⟨targetExitEnv,?_,?_,exitFrame,exitLocals,?_⟩
  · simpa only [wordSemContLoop, Bool.false_eq_true, if_false, if_true, sourceExitState] using sourceLoop
  · simpa only [wordSemContLoop, Bool.false_eq_true, if_false, if_true, targetExitState] using targetLoop
  · rw [pure_loop_cost_run SP names exits body source sourceEntry sourcePost
      (some (.break 0)) sourceCut sourceRun]
    rw [pure_loop_cost_run TP
      (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names)
      (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits)
      (match (generalizing := false) moves with | .skip => output | _ => .seq output moves)
      target targetEntry targetPost
      (some (.break 0)) targetCut finalRun]
    cases moves <;> dsimp only at finalCost headCost ⊢
    all_goals simpa only [finalCost, wordSemContLoop, Bool.false_eq_true, if_false, Nat.add_zero]
      using Nat.add_le_add headCost bodyCost

#print axioms ssa_loop_break_zero_cost
#print axioms ssa_loop_exit_cut
end InitECandidate.Runtime.FineCost
