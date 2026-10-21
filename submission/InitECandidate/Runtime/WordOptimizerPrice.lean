import InitECandidate.Runtime.WordOptimizerMoveCost
import InitECandidate.Runtime.WordExecutionCostProps

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Runtime.WordToStack

/-- Intermediate post-instruction-selection price. Parallel assignments pay
for their input pairs, so physical renaming and merge scheduling need no
unproved invariance of the final allocated scheduler. Other nodes retain the
canonical compiler-fragment prices. Assign expressions are still excluded by
the post-selection eligibility obligation. -/
noncomputable def wordOptimizerLocalPrice {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) : Nat :=
  match program with
  | .move _ pairs => 24 * pairs.length
  | _ => refinedWordLocalPrice program source

theorem refinedWordLocalPrice_le_optimizer {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    refinedWordLocalPrice program source ≤ wordOptimizerLocalPrice program source := by
  cases program <;> try exact Nat.le_refl _
  case move priority pairs =>
    simpa only [refinedWordLocalPrice, refinedWordStackLeafBudget,
      wordOptimizerLocalPrice, id_eq] using renamed_parallel_moves_cost_le id pairs

theorem refinedWordExecutionCost_le_optimizer {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost refinedWordLocalPrice program source ≤
      wordExecutionCost wordOptimizerLocalPrice program source := by
  exact wordExecutionCost_mono refinedWordLocalPrice wordOptimizerLocalPrice
    refinedWordLocalPrice_le_optimizer program source

/-- A whole actual Word execution with the intermediate optimizer price
already pays the checked Word-to-Stack cost, with coefficient one. This is a
downstream endpoint for optimization/colouring transfers, not a source bound. -/
theorem optimizerWordCost_correct {F : Type} (ac : Compiler.Encoders.Asm.AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (supported : wordCostSupported program = true) (code : CostSupportedCode source.code)
    (frames : CodeFramesBounded source.code source.stackSize 92) :
    RefinedExecutedSimulation ac program source
      (wordExecutionCost wordOptimizerLocalPrice program source) := by
  exact (refinedWordCost_correct ac program source supported code frames).mono
    (refinedWordExecutionCost_le_optimizer program source)

theorem optimizer_move_merge_subadditive {C F : Type}
    (first second : List (Nat × Nat)) (priority : Nat)
    (source : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.move priority (WordUnreach.mergeMoves first second)) source ≤
      wordOptimizerLocalPrice (.move priority first) source +
      wordOptimizerLocalPrice (.move priority second) source := by
  have bound := mergeMoves_length_le first second
  simp only [wordOptimizerLocalPrice]
  omega

#print axioms optimizerWordCost_correct
#print axioms optimizer_move_merge_subadditive
end InitECandidate.Runtime.FineCost
