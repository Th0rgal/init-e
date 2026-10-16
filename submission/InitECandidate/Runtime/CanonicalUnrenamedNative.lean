import InitECandidate.Runtime.PanFunctionRenameClock
import InitECandidate.Runtime.CanonicalRenamedNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Native bound from an original-named source main run, retaining its clock. -/
theorem canonical_unrenamed_return_native (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({canonicalUnrenamedSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + 1 + baselineCrepExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  have renamed := canonical_source_entry_rename_run input fuel (some (.returned value)) post run
  exact canonical_renamed_return_native input fuel
    {post with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart post.code)} value renamed

#print axioms canonical_unrenamed_return_native

/-- Native bound from an original-named source main run, retaining its clock. -/
theorem canonical_unrenamed_ffi_native (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({canonicalUnrenamedSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + 1 + baselineCrepExtraFuel (fuel + 1)) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  have renamed := canonical_source_entry_rename_run input fuel (some (.finalFfi event)) post run
  exact canonical_renamed_ffi_native input fuel
    {post with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart post.code)} event renamed

#print axioms canonical_unrenamed_ffi_native
end InitECandidate.Runtime
