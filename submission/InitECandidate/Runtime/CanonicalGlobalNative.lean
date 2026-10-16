import InitECandidate.Runtime.BaselineGlobalsClock
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- The concrete global wrapper adds one clock before native compilation. -/
theorem canonical_global_return_native (input : Guest.InputBlob)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : PanSemStateFiniteExact.evaluateHOLFiniteState
      {canonicalPanEntryState input with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({initialized with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + 1 + baselineCrepExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wrapped,wrappedRun,ffi⟩ := canonical_global_entry_clock input initialized
    initialRun fuel (some (.returned value)) post run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_pan_return_native input (fuel + 1) wrapped value wrappedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_global_return_native

/-- The concrete global wrapper adds one clock before native compilation. -/
theorem canonical_global_ffi_native (input : Guest.InputBlob)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : PanSemStateFiniteExact.evaluateHOLFiniteState
      {canonicalPanEntryState input with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({initialized with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + 1 + baselineCrepExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wrapped,wrappedRun,ffi⟩ := canonical_global_entry_clock input initialized
    initialRun fuel (some (.finalFfi event)) post run
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_pan_ffi_native input (fuel + 1) wrapped event wrappedRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_global_ffi_native
end InitECandidate.Runtime
