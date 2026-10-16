import InitECandidate.Runtime.PanFunctionTables
import InitECandidate.Runtime.BaselinePanEntryFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang InitECandidate.Proofs

/-- Actual generated declarations pass all original shape and duplicate
exception-name initialization checks. -/
theorem baseline_pan_declaration_setup :
    panDeclarationSetup (width := 64) [] HolFiniteMapExact.empty FrontendStages.pass2 = true := by
  decide_cbv

#print axioms baseline_pan_declaration_setup
end InitECandidate.Runtime
