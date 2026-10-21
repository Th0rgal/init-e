import InitECandidate.Runtime.WordPostSSACodeTable
import InitECandidate.Runtime.WordCallExecutionCost
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Call
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Flat-convention evidence for every actual function-table lookup. -/
def PostSSAFlatCode (code : Spt (Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  ∀ destination arity body, sptLookup destination code = some (arity, body) →
    flatExpConventions body = true

/-- The global induction hypothesis transports unchanged syntax through the
optimized function table. It is guarded by termination depth and clock;
MustTerminate can reset clock, so clock alone would be unsound here. The
same-code local optimization theorem is applied after this transport. -/
def PostSSACodeTransportIH {C F : Type} (depth clock : Nat) : Prop :=
  ∀ (program : WordLangProgHOL (BitVec 64)) (source post : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)),
    Prod.Lex (· < ·) (· < ·) (source.termdep, source.clock) (depth, clock) →
    noInstallSubprogsHOL program = true → WordProps.noInstallCode source.code →
    PostSSAFlatCode source.code → evaluate program source = (result, post) →
    result ≠ some .error →
    evaluate program {source with code := postSSACodeTable source.code} =
      (result, {post with code := postSSACodeTable source.code}) ∧
    wordExecutionCost wordOptimizerLocalPrice program
      {source with code := postSSACodeTable source.code} ≤
      wordExecutionCost wordOptimizerLocalPrice program source

/-- A tail call through the actual optimized function table. The guarded
hypothesis runs the original callee over the new table; the checked local
optimizer then runs the transformed callee. No transformed-callee execution
or cost bound is an unguarded premise. -/
theorem postSSACodeTable_tail_execution {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (destination : Option Nat) (arguments : List Nat) (source : WordSemStateFiniteExact 64 C F)
    (codeFree : WordProps.noInstallCode source.code) (codeFlat : PostSSAFlatCode source.code)
    (safe : (evaluate (.call none destination arguments none) source).1 ≠ some .error)
    (ih : PostSSACodeTransportIH (C := C) (F := F) source.termdep source.clock) :
    evaluate (.call none destination arguments none)
        {source with code := postSSACodeTable source.code} =
      ((evaluate (.call none destination arguments none) source).1,
        {(evaluate (.call none destination arguments none) source).2 with
          code := postSSACodeTable source.code}) ∧
    wordExecutionCost wordOptimizerLocalPrice (.call none destination arguments none)
        {source with code := postSSACodeTable source.code} ≤
      wordExecutionCost wordOptimizerLocalPrice (.call none destination arguments none) source := by
  rw [WordToWord.evaluate_call_eq] at safe
  rcases hg : getVars arguments source with _ | xs
  · simp only [hg] at safe
    exact (safe rfl).elim
  simp only [hg] at safe
  by_cases bad : wordSemBadDestArgs destination arguments = true
  · simp only [bad, if_true] at safe
    exact (safe rfl).elim
  have good : wordSemBadDestArgs destination arguments = false := by simpa using bad
  simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc] at safe
  rcases found : wordSemFindCode destination xs source.code source.stackSize with
    _ | ⟨actualArguments, body, size⟩
  · simp only [found] at safe
    exact (safe rfl).elim
  simp only [found] at safe
  let target : WordSemStateFiniteExact 64 C F :=
    {source with code := postSSACodeTable source.code}
  have targetVars : getVars arguments target = some xs := by
    rw [(getVars_congr target source rfl arguments).symm]
    exact hg
  have targetFound : wordSemFindCode destination xs target.code target.stackSize =
      some (actualArguments, postSSAOptimize body, size) := by
    rw [show target.code = postSSACodeTable source.code from rfl,
      show target.stackSize = source.stackSize from rfl, postSSACodeTable_findCode, found]
    rfl
  have targetClock : target.clock = source.clock := rfl
  change evaluate (.call none destination arguments none) target = _ ∧
    wordExecutionCost wordOptimizerLocalPrice (.call none destination arguments none) target ≤ _
  by_cases zero : source.clock = 0
  · constructor
    · rw [WordToWord.evaluate_call_eq, targetVars]
      simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, targetFound,
        targetClock, zero, if_true]
      rw [WordToWord.evaluate_call_eq, hg]
      simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, zero, if_true]
      rfl
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [targetVars, hg, good, Bool.false_eq_true, if_false, wordSemAddRetLoc,
        targetFound, found, targetClock, zero, dif_pos rfl]
      simpa only [dif_pos True.intro] using
        le_of_eq (wordOptimizerLocalPrice_state_independent (.call none destination arguments none) target source)
  simp only [zero, if_false] at safe
  let entry := callEnv actualArguments size (decClock source)
  rcases actual : evaluate body entry with ⟨result, post⟩
  have entryRun : evaluate body (callEnv actualArguments size (decClock source)) = (result, post) := actual
  rw [entryRun] at safe
  have valid : wordSemBadFunReturn result = false := by
    by_cases invalid : wordSemBadFunReturn result = true
    · simp only [invalid, if_true] at safe
      exact (safe rfl).elim
    · simpa using invalid
  have resultSafe : result ≠ some .error := by
    simpa only [valid, Bool.false_eq_true, if_false] using safe
  have terminal : result ≠ none ∧ (∀ label, result ≠ some (.break label)) ∧
      (∀ label, result ≠ some (.continue label)) := by
    cases result with
    | none => simp [wordSemBadFunReturn] at valid
    | some outcome => cases outcome <;> simp_all [wordSemBadFunReturn]
  have smaller : Prod.Lex (· < ·) (· < ·)
      (entry.termdep, entry.clock) (source.termdep, source.clock) := by
    simp only [entry, WordSemStateFiniteExact.callEnv, decClock]
    apply Prod.Lex.right
    omega
  have bodyFree := WordProps.noInstallFindCode source.code destination xs source.stackSize
    actualArguments body size ⟨codeFree, found⟩
  obtain ⟨label, arity, lookup⟩ := WordProps.findCode_lookup source.code destination xs
    source.stackSize actualArguments body size found
  have bodyFlat := codeFlat label arity body lookup
  obtain ⟨transported, transportCost⟩ := ih body entry post result smaller bodyFree
    codeFree codeFlat actual resultSafe
  obtain ⟨optimized, optimizeCost⟩ := postSSAOptimize_terminal_execution config body
    {entry with code := postSSACodeTable entry.code}
    {post with code := postSSACodeTable entry.code} result bodyFlat transported resultSafe terminal
  have targetEntry : callEnv actualArguments size (decClock target) =
      {entry with code := postSSACodeTable entry.code} := rfl
  have targetRun : evaluate (postSSAOptimize body)
      (callEnv actualArguments size (decClock target)) =
        (result, {post with code := postSSACodeTable source.code}) := by
    rw [targetEntry]
    exact optimized
  constructor
  · change evaluate (.call none destination arguments none) target = _
    rw [WordToWord.evaluate_call_eq, targetVars]
    simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, targetFound]
    rw [if_neg zero, targetRun]
    simp only [valid, Bool.false_eq_true, if_false]
    rw [WordToWord.evaluate_call_eq, hg]
    simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found,
      zero, if_false, entryRun, valid]
  · change wordExecutionCost wordOptimizerLocalPrice (.call none destination arguments none) target ≤ _
    rw [tail_call_cost _ destination arguments target xs targetVars good actualArguments
        (postSSAOptimize body) size targetFound zero,
      tail_call_cost _ destination arguments source xs hg good actualArguments body size found zero,
      wordOptimizerLocalPrice_state_independent (.call none destination arguments none) target source]
    apply Nat.add_le_add_left
    rw [targetEntry]
    exact optimizeCost.trans transportCost

#print axioms postSSACodeTable_tail_execution
end InitECandidate.Runtime.FineCost
