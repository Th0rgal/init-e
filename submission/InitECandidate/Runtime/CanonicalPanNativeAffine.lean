import InitECandidate.Runtime.CanonicalPanNative
import InitECandidate.Runtime.CanonicalCrepNativeAffine
import InitECandidate.Runtime.BaselinePanEntryFacts
import InitECandidate.Runtime.PanExceptionDomain
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
import InitECandidate.Runtime.BaselineFrontendNativeAffine
import InitECandidate.Runtime.BaselineNativeOutcomesAffine
import InitECandidate.Runtime.BaselineLoopNativeAffine
import InitECandidate.Runtime.BaselineCrepNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Original global-lowered Pancake entry execution yields the actual
installed native run with all concrete compiler/initialization guards internal. -/
theorem canonical_pan_return_native_affine (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({canonicalPanEntryState input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none baselineCrepStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + baselineCrepAffineExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨crepPost,crepRun,postState,postCode,postExc,initialClock,finalClock,ffi⟩ :=
    pan_crep_entry_return_same_clock
      {canonicalPanEntryState input with clock := fuel} {canonicalCrepState input with clock := fuel}
      FrontendStages.pass2 baselineCrepStart (canonical_pan_crep_state input fuel)
      baseline_pan_distinct rfl (canonical_crep_code input) rfl baseline_pan_localised
      baseline_pan_eids_size (pan_exception_table_domain FrontendStages.pass2) post value run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_crep_return_native_affine input fuel crepPost (flattenHOL value) crepRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_pan_return_native_affine
/-- Original global-lowered Pancake entry execution yields the actual
installed native run with all concrete compiler/initialization guards internal. -/
theorem canonical_pan_ffi_native_affine (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({canonicalPanEntryState input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none baselineCrepStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + baselineCrepAffineExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨crepPost,crepRun,postState,postCode,postExc,initialClock,finalClock,ffi⟩ :=
    pan_crep_entry_ffi_same_clock
      {canonicalPanEntryState input with clock := fuel} {canonicalCrepState input with clock := fuel}
      FrontendStages.pass2 baselineCrepStart (canonical_pan_crep_state input fuel)
      baseline_pan_distinct rfl (canonical_crep_code input) rfl baseline_pan_localised
      baseline_pan_eids_size (pan_exception_table_domain FrontendStages.pass2) post event run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_crep_ffi_native_affine input fuel crepPost event crepRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_pan_ffi_native_affine
end InitECandidate.Runtime
