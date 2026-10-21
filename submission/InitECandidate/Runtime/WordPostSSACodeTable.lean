import InitECandidate.Runtime.WordPostSSAOptimizerCost
import Flapjack.Compiler.Backend.WordRemove.Proofs.CompileState
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Frame
import Flapjack.Misc.Sptree.Map

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Concrete whole-table version of the checked local post-SSA fragment.
Arity, labels and stack-size metadata are unchanged. -/
def postSSACodeTable (code : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    Spt (Nat × WordLangProgHOL (BitVec 64)) :=
  sptMap (fun entry => (entry.1, postSSAOptimize entry.2)) code

theorem postSSACodeTable_lookup (code : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (destination : Nat) :
    sptLookup destination (postSSACodeTable code) =
      (sptLookup destination code).map (fun entry => (entry.1, postSSAOptimize entry.2)) := by
  exact sptLookup_sptMap _ _ _

theorem postSSACodeTable_mem (code : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (destination : Nat) : sptMem destination (postSSACodeTable code) = sptMem destination code := by
  apply propext
  rw [sptMem_iff_lookup, sptMem_iff_lookup]
  rw [postSSACodeTable_lookup]
  cases sptLookup destination code <;> simp

/-- Both direct and indirect lookup use the actual code-table map; neither a
callee identity nor an abstract lookup-relation hypothesis is required. -/
theorem postSSACodeTable_findCode (destination : Option Nat) (arguments : List (WordLocW 64))
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (sizes : Spt Nat) :
    wordSemFindCode destination arguments (postSSACodeTable code) sizes =
      (wordSemFindCode destination arguments code sizes).map
        (fun found => (found.1, postSSAOptimize found.2.1, found.2.2)) := by
  exact WordRemove.findCode_map_I destination arguments postSSAOptimize code sizes

/-- The local optimizer preserves the flat-expression convention required
by each subsequent stage, for the exact pinned pass order. -/
theorem postSSAOptimize_flat (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64)) (flat : flatExpConventions program = true) :
    flatExpConventions (postSSAOptimize program) = true := by
  have first := (WordConvs.removeDeadProgConventions (fun _ => true) program config).1 flat
  have cse := WordConvs.flat_exp_conventions_word_common_subexp_elim _ first
  have copy := WordConvs.flat_exp_conventions_copy_prop _ cse
  have unreach := WordConvs.flatExpConventions_removeUnreach _ copy
  exact (WordConvs.removeDeadProgConventions (fun _ => true) _ config).1 unreach

/-- Terminal function outcomes have exact locals after removeDead; only
fall-through and loop control use its weaker postcondition. This is needed
when a transformed callee returns to its caller. -/
theorem postSSAOptimize_terminal_execution {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64)) (source post : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)) (flat : flatExpConventions program = true)
    (run : evaluate program source = (result, post)) (safe : result ≠ some .error)
    (terminal : result ≠ none ∧ (∀ label, result ≠ some (.break label)) ∧
      (∀ label, result ≠ some (.continue label))) :
    evaluate (postSSAOptimize program) source = (result, post) ∧
      wordExecutionCost wordOptimizerLocalPrice (postSSAOptimize program) source ≤
        wordExecutionCost wordOptimizerLocalPrice program source := by
  obtain ⟨locals, targetRun, related, cost⟩ :=
    postSSAOptimize_executed_correct config program source post result flat run safe
  have equal : post.locals = locals := by
    cases result with
    | none => exact (terminal.1 rfl).elim
    | some outcome =>
      cases outcome <;> simp_all [RemoveDeadProgPost]
  subst locals
  exact ⟨targetRun, cost⟩

open Flapjack.Compiler.Backend.WordToWord in
/-- Changing to the concrete optimized code table is an exact semantic frame
for a non-installing atomic statement. It also leaves its executed price
unchanged. This is the leaf case of the whole-table induction, not a claim
that calls through the new table are already proved. -/
theorem postSSACodeTable_leaf_execution {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (leaf : cscLeaf program = true) :
    evaluate program {source with code := postSSACodeTable source.code} =
      ((evaluate program source).1,
        {(evaluate program source).2 with code := postSSACodeTable source.code}) ∧
    wordExecutionCost wordOptimizerLocalPrice program
      {source with code := postSSACodeTable source.code} =
      wordExecutionCost wordOptimizerLocalPrice program source := by
  have frame := evaluate_tgt_frame (postSSACodeTable source.code) source.compileOracle source.compile
    source (fun n => postSSACodeTable_mem source.code n) program leaf
  have self := evaluate_tgt_frame source.code source.compileOracle source.compile source
    (fun _ => rfl) program leaf
  have oracle := congrArg (fun output => output.2.compileOracle) self
  have compiler := congrArg (fun output => output.2.compile) self
  change (evaluate program source).2.compileOracle = source.compileOracle at oracle
  change (evaluate program source).2.compile = source.compile at compiler
  constructor
  · simpa only [tgtState, ← oracle, ← compiler] using frame
  · have atomic : wordCostAtomic program = true := by
      cases program <;> simp_all [cscLeaf, wordCostAtomic]
    rw [wordExecutionCost_atomic _ _ _ atomic, wordExecutionCost_atomic _ _ _ atomic]
    exact wordOptimizerLocalPrice_state_independent _ _ _

#print axioms postSSACodeTable_findCode
#print axioms postSSAOptimize_flat
#print axioms postSSAOptimize_terminal_execution
#print axioms postSSACodeTable_leaf_execution
end InitECandidate.Runtime.FineCost
