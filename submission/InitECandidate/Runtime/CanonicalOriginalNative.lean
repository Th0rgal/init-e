import InitECandidate.Runtime.CanonicalOriginalSourceEntry
import InitECandidate.Runtime.PanSimpEntryClock
import InitECandidate.Runtime.CanonicalUnrenamedNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Original challenge-source main execution gives an actual installed native
run with a bounded clock, preserving the original resource-limit alternative. -/
theorem canonical_original_return_native (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({canonicalOriginalSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + 1 + baselineCrepExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨simplifiedPost,simplifiedRun,ffi,clock,related⟩ := pan_simp_entry_same_clock
    (canonicalOriginalSourceEntry input) (canonicalUnrenamedSourceEntry input)
    FrontendStages.Declarations.globalStart fuel (canonical_original_simplified_relation input)
    (some (.returned value)) post run (by simp)
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_unrenamed_return_native input fuel simplifiedPost value simplifiedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_original_return_native

/-- Original challenge-source main execution gives an actual installed native
run with a bounded clock, preserving the original resource-limit alternative. -/
theorem canonical_original_ffi_native (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({canonicalOriginalSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + 1 + baselineCrepExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨simplifiedPost,simplifiedRun,ffi,clock,related⟩ := pan_simp_entry_same_clock
    (canonicalOriginalSourceEntry input) (canonicalUnrenamedSourceEntry input)
    FrontendStages.Declarations.globalStart fuel (canonical_original_simplified_relation input)
    (some (.finalFfi event)) post run (by simp)
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_unrenamed_ffi_native input fuel simplifiedPost event simplifiedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_original_ffi_native
end InitECandidate.Runtime
