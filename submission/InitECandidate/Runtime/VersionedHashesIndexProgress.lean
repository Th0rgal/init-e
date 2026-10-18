import InitECandidate.Runtime.VersionedHashesLoopSource
import InitECandidate.Runtime.NormalDecLocalFrame
import InitECandidate.Runtime.NormalWhileLocalFrame
import InitECandidate.Runtime.NormalLocalAddCalls
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed blob comparison scan leaves the enclosing transaction
index intact, including its nested declaration scopes and inner loop. -/
theorem versioned_hashes_scan_index_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state versionedHashesScan = (none,post)) :
    post.locals.lookup (ofString "i") = state.locals.lookup (ofString "i") := by
  rw [source_versioned_hashes_scan] at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      cases run
      rfl
    · refine normalLocalFrame_dec (ofString "i") _ _ _ _ (by decide) ?_ state post run
      intro G current output childRun
      refine normalLocalFrame_dec (ofString "i") _ _ _ _ (by decide) ?_ current output childRun
      intro H current output loopRun
      rw [source_versioned_hashes_blob_loop] at loopRun
      exact evaluate_normal_while_local_frame (ofString "i") _ _ (by
        simp only [versionedHashesBlobStep,versionedHashesBlobLoop,versionedHashesScan,versionedHashesStep,versionedHashesLoop,
          versionedHashesAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
        rfl) (by
        simp only [versionedHashesBlobStep,versionedHashesBlobLoop,versionedHashesScan,versionedHashesStep,versionedHashesLoop,
          versionedHashesAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
        rfl) current output loopRun
  · cases run

/-- Each normally completed original validation iteration advances its real
transaction index by one. Early returns are covered by the normal-run premise. -/
theorem versioned_hashes_step_adds_one : NormalLocalAdd (ofString "i") 1 versionedHashesStep := by
  rw [source_versioned_hashes_step]
  apply normalLocalAdd_decCall _ _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_decCall _ _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_seq_normal_frame
  · intro F state post run
    exact versioned_hashes_scan_index_frame state post run
  · exact normalLocalAdd_assign _ 1

#print axioms versioned_hashes_scan_index_frame
#print axioms versioned_hashes_step_adds_one
end InitECandidate.Runtime
