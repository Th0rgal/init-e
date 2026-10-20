import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

/-- A closed runtime's oracle cannot introduce any additional code entries. -/
def EmptyInstallOracle {C F : Type} (s : StackSemStateFiniteExact 64 C F) : Prop :=
  ∀ index, (s.compileOracle index).2.1 = []

/-- Original evaluator code/oracle accounting yields exact preservation in a
closed runtime, even for arbitrary evaluator syntax and outcome. -/
theorem evaluate_emptyInstallOracle {C F : Type} (p : HolProg 64)
    (source post : StackSemStateFiniteExact 64 C F) result
    (emptyOracle : EmptyInstallOracle source)
    (run : StackSemEvaluate.evaluate (p, source) = (result, post)) :
    post.code = source.code ∧ EmptyInstallOracle post := by
  obtain ⟨count, oracle, code, bitmaps⟩ := StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p source result post run
  have folded (indices : List Nat) (tree : Spt (HolProg 64)) :
      (indices.map (fun index => sptFromAList (source.compileOracle index).2.1)).foldl sptUnion tree = tree := by
    induction indices generalizing tree with
    | nil => rfl
    | cons index rest ih =>
      simp only [List.map_cons, List.foldl_cons, emptyOracle index, sptFromAList]
      have unionNil : sptUnion tree .ln = tree := by cases tree <;> simp [sptUnion]
      rw [unionNil]
      exact ih tree
  refine ⟨code.trans (folded _ _), ?_⟩
  intro index
  rw [oracle]
  exact emptyOracle _

#print axioms evaluate_emptyInstallOracle
end InitECandidate.Runtime.StackToLab
