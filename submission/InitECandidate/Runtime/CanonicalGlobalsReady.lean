import InitECandidate.Runtime.ZeroGlobalDeclarations
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The fixed source globals always initialize on the actual installed memory. -/
theorem canonical_globals_ready (input : Guest.InputBlob) :
    ∃ initialized, evaluateHOLFiniteState (canonicalPanEntryState input)
        (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized) ∧
      panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalContext (zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames) initialized ∧
      initialized.clock = (canonicalPanEntryState input).clock ∧
      initialized.ffi = (canonicalPanEntryState input).ffi ∧
      initialized.locals = (canonicalPanEntryState input).locals ∧
      panGlobalsByteAlignedHOL FrontendStages.Declarations.globalContext.globalsSize :=
  canonical_globals_initialize input _ (canonical_source_globals_evaluate input)

noncomputable def canonicalInitializedGlobals (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  Classical.choose (canonical_globals_ready input)

theorem canonical_globals_ready_run (input : Guest.InputBlob) :
    evaluateHOLFiniteState (canonicalPanEntryState input)
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) =
      (none,canonicalInitializedGlobals input) :=
  (Classical.choose_spec (canonical_globals_ready input)).1

theorem canonical_globals_ready_relation (input : Guest.InputBlob) :
    panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalContext
      (zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames)
      (canonicalInitializedGlobals input) :=
  (Classical.choose_spec (canonical_globals_ready input)).2.1

#print axioms canonical_globals_ready
#print axioms canonical_globals_ready_run
#print axioms canonical_globals_ready_relation
end InitECandidate.Runtime
