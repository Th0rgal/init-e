import InitECandidate.Runtime.CanonicalSourceFunctionsEvaluated
import InitECandidate.Runtime.CanonicalSourceExceptionsEvaluated
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

theorem baseline_source_declaration_kinds :
    FrontendStages.pass1.all (fun declaration =>
      isFunctionHOL declaration || isDeclHOL declaration || isExnDeclHOL declaration) = true := by decide_cbv

/-- The actual pre-global-lowering declarations evaluate to precisely the
original-named source entry used by the quantitative native execution theorem. -/
theorem canonical_source_declarations_evaluate (input : Guest.InputBlob) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      FrontendStages.pass1 = some (canonicalUnrenamedSourceEntry input) := by
  classical
  have reordered : evaluateDeclsHOLFinite (sourceInitialState input)
      (resortDeclsHOL FrontendStages.pass1) = some (canonicalUnrenamedSourceEntry input) := by
    change evaluateDeclsHOLFinite (sourceInitialState input)
      (resortDeclsHOL FrontendStages.Declarations.simplifieds) = _
    rw [FrontendStages.Declarations.sourceResort_eq]
    rw [Flapjack.evaluateDeclsHOLFinite_append,Flapjack.evaluateDeclsHOLFinite_append,canonical_source_exceptions_evaluate]
    simp only [Option.bind_some]
    rw [canonical_source_globals_evaluate]
    simp only [Option.bind_some]
    exact canonical_source_functions_evaluate input
  rw [resortDeclsEvaluate (sourceInitialState input) FrontendStages.pass1 baseline_source_declaration_kinds] at reordered
  exact reordered

#print axioms baseline_source_declaration_kinds
#print axioms canonical_source_declarations_evaluate
end InitECandidate.Runtime
