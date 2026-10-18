import InitECandidate.Runtime.VersionedHashesIndexProgress
import InitECandidate.Runtime.NormalDecCallLocalFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed blob comparison scan leaves the enclosing transaction
count intact, including its nested declaration scopes and inner loop. -/
theorem versioned_hashes_scan_count_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state versionedHashesScan = (none,post)) :
    post.locals.lookup (ofString "ntx") = state.locals.lookup (ofString "ntx") := by
  rw [source_versioned_hashes_scan] at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      cases run
      rfl
    · refine normalLocalFrame_dec (ofString "ntx") _ _ _ _ (by decide) ?_ state post run
      intro G current output childRun
      refine normalLocalFrame_dec (ofString "ntx") _ _ _ _ (by decide) ?_ current output childRun
      intro H current output loopRun
      rw [source_versioned_hashes_blob_loop] at loopRun
      exact evaluate_normal_while_local_frame (ofString "ntx") _ _ (by
        simp only [versionedHashesBlobStep,versionedHashesBlobLoop,versionedHashesScan,versionedHashesStep,versionedHashesLoop,
          versionedHashesAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
        rfl) (by
        simp only [versionedHashesBlobStep,versionedHashesBlobLoop,versionedHashesScan,versionedHashesStep,versionedHashesLoop,
          versionedHashesAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
        rfl) current output loopRun
  · cases run

theorem versioned_hashes_step_count_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    post.locals.lookup (ofString "ntx") = state.locals.lookup (ofString "ntx") := by
  rw [source_versioned_hashes_step] at run
  refine normalLocalFrame_decCall (ofString "ntx") _ _ _ _ _ (by decide) ?_ state post run
  intro G current output childRun
  refine normalLocalFrame_decCall (ofString "ntx") _ _ _ _ _ (by decide) ?_ current output childRun
  intro H current output tailRun
  rw [evaluateHOLFiniteState_seq_line780] at tailRun
  cases scanned : evaluateHOLFiniteState current versionedHashesScan with
  | mk result middle =>
    rw [scanned] at tailRun
    cases result with
    | some result => cases tailRun
    | none =>
      dsimp only at tailRun
      have kept := versioned_hashes_scan_count_frame current middle scanned
      have updated := evaluate_straight_local_frame (ofString "ntx")
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (by decide) middle
      rw [tailRun] at updated
      exact updated.trans kept

#print axioms versioned_hashes_scan_count_frame
#print axioms versioned_hashes_step_count_frame
end InitECandidate.Runtime
