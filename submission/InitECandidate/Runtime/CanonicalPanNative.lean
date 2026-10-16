import InitECandidate.Runtime.CanonicalCrepNative
import InitECandidate.Runtime.BaselinePanEntryFacts
import InitECandidate.Runtime.PanExceptionDomain
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Initialized global-lowered Pancake carrier with the concrete generated
function/exception tables and canonical frontend memory, heap and FFI fields. -/
noncomputable def canonicalPanEntryState (input : Guest.InputBlob) : PanSemStateFiniteExact 64 Guest.HostMemory where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty.updateList (functionsHOL FrontendStages.pass2).reverse
  eshapes := HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.pass2)
  memory := (canonicalCrepState input).memory
  memaddrs := (canonicalCrepState input).memaddrs
  shMemaddrs := (canonicalCrepState input).shMemaddrs
  clock := (canonicalCrepState input).clock
  be := (canonicalCrepState input).be
  ffi := (canonicalCrepState input).ffi
  baseAddr := (canonicalCrepState input).baseAddr
  topAddr := (canonicalCrepState input).topAddr

theorem canonical_pan_crep_state (input : Guest.InputBlob) (fuel : Nat) :
    panToCrepStateRelFiniteExact {canonicalPanEntryState input with clock := fuel}
      {canonicalCrepState input with clock := fuel} :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem canonical_crep_code (input : Guest.InputBlob) :
    (canonicalCrepState input).code =
      HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW FrontendStages.pass2).reverse := by
  change HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse = _
  rw [FrontendStages.toCrep_eq]

/-- Original global-lowered Pancake entry execution yields the actual
installed native run with all concrete compiler/initialization guards internal. -/
theorem canonical_pan_return_native (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({canonicalPanEntryState input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none baselineCrepStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + baselineCrepExtraFuel fuel) ∧
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
    canonical_crep_return_native input fuel crepPost (flattenHOL value) crepRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_pan_return_native
/-- Original global-lowered Pancake entry execution yields the actual
installed native run with all concrete compiler/initialization guards internal. -/
theorem canonical_pan_ffi_native (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({canonicalPanEntryState input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none baselineCrepStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + baselineCrepExtraFuel fuel) ∧
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
    canonical_crep_ffi_native input fuel crepPost event crepRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms canonical_pan_ffi_native
end InitECandidate.Runtime
