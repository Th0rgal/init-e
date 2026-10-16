import InitECandidate.Runtime.BaselineCompilerProjection
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.LabToTarget
open InitE Flapjack Flapjack.Pancake.Proofs.PanToTarget

private theorem result_of_projection {A B : Type} (result : A × B) (value : A)
    (projection : result.1 = value) : ∃ rest, result = (value, rest) := by
  cases result with
  | mk first second => exact ⟨second, congrArg (fun x => (x, second)) projection⟩

/-- Retain the logical stack-depth result opaquely while recovering the full
compiler result from its certified artifact. -/
theorem baseline_compiler_result : ∃ depth,
    compileProgMax baselineCompilerConfig baselineMachineConfig sourceDeclarations =
      (some (InitECandidate.nativeCode, InitECandidate.bitmaps, baselineConfig), depth) :=
  result_of_projection _ _ baseline_compiler_projection

#print axioms baseline_compiler_result
end InitECandidate.Runtime.LabToTarget
