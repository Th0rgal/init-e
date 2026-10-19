import InitECandidate.Runtime.EndpointCanonicalPanNative
import InitECandidate.Runtime.EndpointCanonicalCrepNativeAffine
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
theorem endpoint_canonical_pan_return_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({endpoint_canonicalPanEntryState input endpoint related with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none baselineCrepStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + baselineCrepAffineExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨crepPost,crepRun,postState,postCode,postExc,initialClock,finalClock,ffi⟩ :=
    pan_crep_entry_return_same_clock
      {endpoint_canonicalPanEntryState input endpoint related with clock := fuel} {endpoint_canonicalCrepState input endpoint related with clock := fuel}
      FrontendStages.pass2 baselineCrepStart (endpoint_canonical_pan_crep_state input endpoint related fuel)
      baseline_pan_distinct rfl (endpoint_canonical_crep_code input endpoint related) rfl baseline_pan_localised
      baseline_pan_eids_size (pan_exception_table_domain FrontendStages.pass2) post value run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_crep_return_native_affine input endpoint related fuel crepPost (flattenHOL value) crepRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms endpoint_canonical_pan_return_native_affine
/-- Original global-lowered Pancake entry execution yields the actual
installed native run with all concrete compiler/initialization guards internal. -/
theorem endpoint_canonical_pan_ffi_native_affine (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({endpoint_canonicalPanEntryState input endpoint related with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none baselineCrepStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + baselineCrepAffineExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨crepPost,crepRun,postState,postCode,postExc,initialClock,finalClock,ffi⟩ :=
    pan_crep_entry_ffi_same_clock
      {endpoint_canonicalPanEntryState input endpoint related with clock := fuel} {endpoint_canonicalCrepState input endpoint related with clock := fuel}
      FrontendStages.pass2 baselineCrepStart (endpoint_canonical_pan_crep_state input endpoint related fuel)
      baseline_pan_distinct rfl (endpoint_canonical_crep_code input endpoint related) rfl baseline_pan_localised
      baseline_pan_eids_size (pan_exception_table_domain FrontendStages.pass2) post event run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_canonical_crep_ffi_native_affine input endpoint related fuel crepPost event crepRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms endpoint_canonical_pan_ffi_native_affine
end InitECandidate.Runtime
