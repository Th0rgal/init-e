import InitECandidate.Runtime.StackBitmapInvariant
import InitECandidate.Runtime.BaselineStackEntryCeiling
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend

theorem entryStackState_emptyBitmapOracle {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackRemove.EmptyBitmapOracle {entryStackState entry.cfg entry.source with clock := fuel} := by
  exact ⟨fun _ => rfl⟩

theorem entryNamedState_emptyBitmapOracle {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackRemove.EmptyBitmapOracle (entryNamedState entry fuel) := by
  exact ⟨fun _ => rfl⟩

/-- No execution from the actual compiled Stack entry grows its bitmap table. -/
theorem baseline_stack_bitmaps_unchanged {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (program : Compiler.Backend.StackLang.HolProg 64)
    (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (run : StackSemEvaluate.evaluate
      (program, {entryStackState entry.cfg entry.source with clock := fuel}) = (result,post)) :
    post.bitmaps = (entryStackState entry.cfg entry.source).bitmaps :=
  ((entryStackState_emptyBitmapOracle entry fuel).of_evaluate run).2

#print axioms entryStackState_emptyBitmapOracle
#print axioms entryNamedState_emptyBitmapOracle
#print axioms baseline_stack_bitmaps_unchanged
end InitECandidate.Runtime
