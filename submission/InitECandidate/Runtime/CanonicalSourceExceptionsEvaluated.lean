import InitECandidate.Runtime.CanonicalSourceEntryFields
import InitECandidate.Runtime.PanDeclarationSetup
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

theorem baseline_source_exceptions_setup :
    panDeclarationSetup [] HolFiniteMapExact.empty FrontendStages.Declarations.exceptionDeclarations = true := by decide_cbv

theorem baseline_source_exceptions_functions :
    functionsHOL FrontendStages.Declarations.exceptionDeclarations = [] := by kernel_rfl

theorem baseline_source_exceptions_table :
    exceptionsHOL FrontendStages.pass2 = exceptionsHOL FrontendStages.Declarations.exceptionDeclarations := by kernel_rfl

theorem canonical_source_exceptions_evaluate (input : Guest.InputBlob) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      FrontendStages.Declarations.exceptionDeclarations = some (canonicalGlobalsSourceState input) := by
  classical
  have evaluated := panDeclarationSetup_evaluates FrontendStages.Declarations.exceptionDeclarations
    (sourceInitialState input) baseline_source_exceptions_setup
  rw [baseline_source_exceptions_functions] at evaluated
  have shapes : (canonicalPanEntryState input).eshapes =
      HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.Declarations.exceptionDeclarations) := by
    change HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.pass2) = _
    rw [baseline_source_exceptions_table]
  have post : {(sourceInitialState input) with
      code := (sourceInitialState input).code.updateList []
      eshapes := (sourceInitialState input).eshapes.updateList
        (exceptionsHOL FrontendStages.Declarations.exceptionDeclarations)} = canonicalGlobalsSourceState input := by
    unfold canonicalGlobalsSourceState
    rw [shapes]
    rfl
  rw [post] at evaluated
  exact evaluated

#print axioms baseline_source_exceptions_setup
#print axioms baseline_source_exceptions_functions
#print axioms baseline_source_exceptions_table
#print axioms canonical_source_exceptions_evaluate
end InitECandidate.Runtime
