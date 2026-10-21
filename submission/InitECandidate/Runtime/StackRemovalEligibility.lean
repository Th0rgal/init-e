import InitECandidate.Runtime.StackEmptyInstallOracle
import InitECandidate.Runtime.StackExecutionEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Source grammar covered by the quantitative stack-removal simulations.
All actual guest primitives are included; unused install/copy-buffer paths
are excluded rather than assigned an unjustified local price. -/
def removalSupported : HolProg 64 → Bool
  | .seq first second | .ite _ _ _ first second => removalSupported first && removalSupported second
  | .loop body => removalSupported body
  | .call none _ _ => true
  | .call (some (body, _, _, _)) _ handler => removalSupported body &&
      (match handler with | none => true | some (hp, _, _) => removalSupported hp)
  | .rawCall _ | .get _ _ | .set _ _ | .opCurrHeap _ _ _ | .stackGetSize _ | .stackSetSize _
    | .stackAlloc _ | .stackFree _ | .stackLoad _ _ | .stackStore _ _ => true
  | p => executionAtomic p
termination_by p => sizeOf p

def RemovalCodeSupported (code : Spt (HolProg 64)) : Prop :=
  ∀ key p, sptLookup key code = some p → removalSupported p = true

/-- Empty installation oracles make static callee eligibility invariant
under every reached source execution. -/
theorem removalCodeSupported_evaluate {C F : Type} (p : HolProg 64)
    (source post : StackSemStateFiniteExact 64 C F) result
    (oracle : EmptyInstallOracle source) (global : RemovalCodeSupported source.code)
    (run : StackSemEvaluate.evaluate (p, source) = (result, post)) :
    RemovalCodeSupported post.code ∧ EmptyInstallOracle post := by
  obtain ⟨code, postOracle⟩ := evaluate_emptyInstallOracle p source post result oracle run
  exact ⟨code ▸ global, postOracle⟩

#print axioms removalCodeSupported_evaluate
end InitECandidate.Runtime.StackToLab
