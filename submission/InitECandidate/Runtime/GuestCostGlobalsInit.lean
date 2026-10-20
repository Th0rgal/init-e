import InitECandidate.Runtime.SourceCostGlobalsInit
import InitECandidate.Proofs.FrontendStages.Pass1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang
open InitECandidate.Proofs.FrontendStages

/-- Every global of the exact `pan_globals` input is initialised by a constant. -/
theorem guest_pass1_const_globals : constGlobalDecls (pass1.filter isDeclHOL) = true := by
  decide_cbv

/-- The number of global initialisers, hence of initialiser stores. -/
theorem guest_pass1_global_count : (pass1.filter isDeclHOL).length = 93 := by
  decide_cbv

#print axioms guest_pass1_const_globals
#print axioms guest_pass1_global_count
end InitECandidate.Runtime.FineCost
