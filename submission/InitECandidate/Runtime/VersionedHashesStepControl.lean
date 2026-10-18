import InitECandidate.Runtime.VersionedHashesLoopSource
import InitECandidate.Runtime.NoLoopControlWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem versioned_hashes_step_no_loop_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state versionedHashesStep).1 ≠ some .break ∧
    (evaluateHOLFiniteState state versionedHashesStep).1 ≠ some .continue := by
  apply evaluate_noLoopControlWhile
  rw [source_versioned_hashes_step,source_versioned_hashes_scan,source_versioned_hashes_blob_loop]
  rfl

#print axioms versioned_hashes_step_no_loop_control
end InitECandidate.Runtime
