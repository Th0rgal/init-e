import InitECandidate.Runtime.CanonicalRenamedNative
import InitECandidate.Runtime.CanonicalGlobalsFunctionRelation
import InitECandidate.Runtime.CanonicalInitializedNativeAffine
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
import InitECandidate.Runtime.BaselineFrontendNativeAffine
import InitECandidate.Runtime.BaselineNativeOutcomesAffine
import InitECandidate.Runtime.BaselineLoopNativeAffine
import InitECandidate.Runtime.BaselineCrepNativeAffine
import InitECandidate.Runtime.CanonicalCrepNativeAffine
import InitECandidate.Runtime.CanonicalPanNativeAffine
import InitECandidate.Runtime.CanonicalGlobalNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Actual renamed-source execution transfers to the installed native code. -/
theorem canonical_renamed_return_native_affine (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({canonicalRenamedSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨targetPost,_,_,compiledRun,related⟩ := pan_globals_same_clock
    (.call none FrontendStages.Declarations.globalNewStart [])
    {canonicalRenamedSourceEntry input with clock := fuel} (some (.returned value))
    FrontendStages.Declarations.globalContext {canonicalInitializedGlobals input with clock := fuel} post
    ⟨canonical_globals_function_relation input fuel,run,by simp⟩
  have call : compileProgExactHOL FrontendStages.Declarations.globalContext
      (.call none FrontendStages.Declarations.globalNewStart []) =
      .call none FrontendStages.Declarations.globalNewStart [] := by
    simp [compileProgExactHOL,compileExpExactHOLList]
  rw [call] at compiledRun
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_initialized_return_native_affine input fuel targetPost value compiledRun
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,ffi,_⟩ := related
  rw [← ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_renamed_return_native_affine

/-- Actual renamed-source execution transfers to the installed native code. -/
theorem canonical_renamed_ffi_native_affine (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({canonicalRenamedSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalNewStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨targetPost,_,_,compiledRun,related⟩ := pan_globals_same_clock
    (.call none FrontendStages.Declarations.globalNewStart [])
    {canonicalRenamedSourceEntry input with clock := fuel} (some (.finalFfi event))
    FrontendStages.Declarations.globalContext {canonicalInitializedGlobals input with clock := fuel} post
    ⟨canonical_globals_function_relation input fuel,run,by simp⟩
  have call : compileProgExactHOL FrontendStages.Declarations.globalContext
      (.call none FrontendStages.Declarations.globalNewStart []) =
      .call none FrontendStages.Declarations.globalNewStart [] := by
    simp [compileProgExactHOL,compileExpExactHOLList]
  rw [call] at compiledRun
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    canonical_initialized_ffi_native_affine input fuel targetPost event compiledRun
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,ffi,_⟩ := related
  rw [← ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_renamed_ffi_native_affine
end InitECandidate.Runtime
